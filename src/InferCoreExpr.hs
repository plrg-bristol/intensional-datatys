{-# LANGUAGE LambdaCase #-}

module InferCoreExpr
  ( inferProg,
  )
where

import Constructors
import Control.Monad.Extra
import Control.Monad.RWS
import CoreArity
import qualified CoreSyn as Core
import Data.Bifunctor
import qualified Data.List as L
import qualified Data.Map as M
import FromCore
import GhcPlugins hiding ((<>), Type)
import InferM
import Pair
import Scheme
import Types

-- Infer set constraints for a subtyping constraint
inferSubType :: Type -> Type -> InferM ()
inferSubType = inferSubTypeStep []
  where
    inferSubTypeStep :: [DataType TyCon] -> Type -> Type -> InferM ()
    inferSubTypeStep ds (Data (Inj x d) as) (Data (Inj y d') as')
      -- Escape from loop if constraints have already been discovered
      | Inj x d `notElem` ds = do
        emit (Dom (Inj x (getName d))) (Dom (Inj y (getName d')))
        mapM_ -- Traverse the slice of a datatype
          ( \k ->
              branch k (Inj x d) $
                zipWithM_ (inferSubTypeStep (Inj x d : ds)) (consInstArgs x as k) (consInstArgs y as' k)
          )
          (tyConDataCons d)
    inferSubTypeStep ds (t11 :=> t12) (t21 :=> t22) =
      inferSubTypeStep ds t21 t11 >> inferSubTypeStep ds t12 t22
    inferSubTypeStep _ _ _ = return ()

-- Infer constraints for a module
inferProg :: CoreProgram -> InferM Context
inferProg [] = return M.empty
inferProg (r : rs) = do
  ctx <- associate r
  ctxs <- putVars ctx (inferProg rs)
  return (ctxs <> ctx)

-- Infer a set of constraints and associate them to qualified type scheme
associate :: CoreBind -> InferM Context
associate r = do
  (ctx, cs) <- listen $ saturate $ inferRec r
  return
    ( ( \s ->
          s -- Add constraints to every type in the recursive group
            { boundvs = domain cs,
              Scheme.constraints = cs
            }
      )
        <$> ctx
    )

-- Infer constraints for a mutually recursive binders
inferRec :: CoreBind -> InferM Context
inferRec (NonRec x e) = M.singleton (getName x) <$> infer e
inferRec (Rec xes) = do
  binds <-
    sequence
      $ M.fromList
      $ bimap
        getName
        ( \e -> do
            rec_scheme <- freshCoreScheme (exprType e)
            return (e, rec_scheme)
        )
        <$> xes
  -- Add binds for recursive calls
  putVars (fmap snd binds) $
    traverse
      ( \(e, rec_scheme) -> do
          scheme <- infer e
          -- Bound recursive calls
          -- Must be bidirectional for mututally recursive groups
          inferSubType (body scheme) (body rec_scheme)
          inferSubType (body rec_scheme) (body scheme)
          return scheme
      )
      binds

-- Infer constraints for a program expression
infer :: CoreExpr -> InferM Scheme
infer (Core.Var v) =
  -- Check if identifier is a constructor
  case isDataConId_maybe v of
    Just k
      -- Ignore typeclass evidence
      | isClassTyCon $ dataConTyCon k -> return (Forall [] Ambiguous)
      | otherwise -> fromCoreCons k
    Nothing -> getVar v
infer l@(Core.Lit _) = freshCoreScheme $ exprType l
infer (Core.App e1 (Core.Type e2)) = do
  t <- freshCoreType e2
  scheme <- infer e1
  case scheme of
    Forall (a : as) b ->
      return $ Forall as (subTyVar a t b) -- Type application
    Forall [] Ambiguous -> return (Forall [] Ambiguous)
    _ -> pprPanic "Type application to monotype!" (ppr (scheme, e2))
infer (Core.App e1 e2) =
  saturate
    ( infer e1 >>= \case
        Forall as Ambiguous -> Forall as Ambiguous <$ infer e2
        -- See FromCore 88 for the case when as /= []
        Forall as (t3 :=> t4) -> do
          t2 <- mono <$> infer e2
          inferSubType t2 t3
          return $ Forall as t4
        _ -> pprPanic "The expression has been given too many arguments!" $ ppr (exprType e1, exprType e2)
    )
infer (Core.Lam x e)
  | isTyVar x = do
    a <- getExternalName x
    infer e >>= \case
      Forall as t -> return $ Forall (a : as) t -- Type abstraction
  | otherwise = do
    t1 <- freshCoreType (varType x)
    putVar (getName x) (Forall [] t1) (infer e) >>= \case
      Forall as t2 -> return $ Forall as (t1 :=> t2)
infer (Core.Let b e) = saturate $ do
  ts <- associate b
  putVars ts $ infer e
infer (Core.Case e bind_e core_ret alts) = saturate $ do
  -- Fresh return type
  ret <- freshCoreType core_ret
  -- Infer expression on which to pattern match
  t0 <- mono <$> infer e
  -- Add the variable under scrutinee to scope
  putVar (getName bind_e) (Forall [] t0) $
    case t0 of
      Data (Inj x d) as -> do
        ks <-
          mapMaybeM
            ( \case
                (Core.DataAlt k, xs, rhs)
                  | not (isBottoming rhs) -> do
                    reach <- isBranchReachable e k
                    if reach
                      then do
                        -- Add constructor arguments introduced by the pattern
                        let ts = M.fromList $ zip (fmap getName xs) (Forall [] <$> consInstArgs x as k)
                        branchWithExpr e k (Inj x d) $ do
                          -- Ensure return type is valid
                          ret_i <- mono <$> putVars ts (infer rhs)
                          inferSubType ret_i ret
                        -- Record constructors
                        return (Just k)
                      else return Nothing
                (Core.LitAlt l, _, _) -> pprPanic "Unexpected literal in datatype pattern!" (ppr l)
                _ -> return Nothing -- Skip defaults until all constructors have been seen
            )
            alts
        case findDefault alts of
          (_, Just rhs) | not (isBottoming rhs) ->
            -- Guard by unseen constructors
            branchAny e (tyConDataCons d L.\\ ks) (Inj x d) $ do
              -- Ensure return type is valid
              ret_i <- mono <$> infer rhs
              inferSubType ret_i ret
          _ -> do
            -- Ensure destructor is total if not nested
            top <- topLevel e
            l <- asks inferLoc
            when top $ emit (Dom (Inj x (getName d))) (Set (mkUniqSet (fmap getName ks)) l)
      _ ->
        -- Unrefinable patterns
        mapM_
          ( \(_, xs, rhs) -> do
              -- Add constructor arguments introduced by the pattern
              ts <- sequence $ M.fromList $ zip (fmap getName xs) (fmap (freshCoreScheme . varType) xs)
              -- Ensure return type is valid
              ret_i <- mono <$> putVars ts (infer rhs)
              inferSubType ret_i ret
          )
          alts
  return (Forall [] ret)
infer (Core.Cast e g) = do
  _ <- infer e
  freshCoreScheme (pSnd $ coercionKind g)
infer (Core.Tick SourceNote {sourceSpan = s} e) = setLoc s $ infer e -- Track location in source text
infer (Core.Tick _ e) = infer e -- Ignore other ticks
infer (Core.Coercion g) = pprPanic "Unexpected coercion" (ppr g)
infer (Core.Type t) = pprPanic "Unexpected type" (ppr t)

isBottoming :: CoreExpr -> Bool
isBottoming e =
  case exprBotStrictness_maybe e of
    Nothing -> exprIsBottom e
    Just (_, _) -> True
