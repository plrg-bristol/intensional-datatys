{-# LANGUAGE LambdaCase #-}

module InferCoreExpr
  ( inferProg,
  )
where

import Constructors
import Control.Monad.Extra
import Control.Monad.RWS
import qualified CoreSyn as Core
import Data.Bifunctor
import qualified Data.List as L
import qualified Data.Map as M
import DataTypes
import FromCore
import GhcPlugins hiding ((<>), Type)
import InferM
import Scheme
import Types

-- Infer constraints for a module
inferProg :: CoreProgram -> InferM Context
inferProg [] = return M.empty
inferProg (r : rs) = do
  ictx <- inferRec r
  ctx <- saturate ictx
  ctxs <- putVars ctx (inferProg rs)
  return (ctxs <> ctx)

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
            rec_scheme <- fromCoreScheme (exprType e)
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

inferSubType :: Type -> Type -> InferM ()
inferSubType = inferSubTypeStep []
  where
    inferSubTypeStep :: [DataType TyCon] -> Type -> Type -> InferM ()
    inferSubTypeStep ds (t11 :=> t12) (t21 :=> t22) =
      inferSubTypeStep ds t21 t11 >> inferSubTypeStep ds t12 t22
    inferSubTypeStep ds (Data (Inj x d) as) (Data (Inj y d') as') =
      unless (Inj x d `elem` ds) $ do
        -- Escape from loop if constraints have already been discovered
        emit (Dom (Inj x (getName d))) (Dom (Inj y (getName d')))
        mapM_ -- Traverse the slice of a datatype
          ( \k ->
              branch k (Inj x d) $
                zipWithM_ (inferSubTypeStep (Inj x d : ds)) (dataConRefinedArgs x as k) (dataConRefinedArgs y as' k)
          )
          (tyConDataCons d)
    inferSubTypeStep _ _ _ = return ()

-- Infer constraints for a program expression
infer :: CoreExpr -> InferM Scheme
infer (Core.Coercion g) = pprPanic "Unexpected coercion" (ppr g)
infer (Core.Type t) = pprPanic "Unexpected type" (ppr t)
infer (Core.Tick SourceNote {sourceSpan = s} e) = setLoc s $ infer e -- Track location in source text
infer (Core.Tick _ e) = infer e -- Ignore other ticks
infer (Core.Cast e _) = do
  _ <- infer e
  return (Mono Ambiguous)
infer (Core.Var v) =
  case isDataConId_maybe v of
    Just k
      -- Ignore typeclass evidence
      | isClassTyCon $ dataConTyCon k -> return $ Mono Ambiguous
      -- Infer constructor
      | otherwise -> do
        scheme <- fromCoreCons k
        case decompType (body scheme) of
          -- Refinable constructor
          (_, Data d _) -> do
            l <- asks inferLoc
            emit (Con (getName k) l) (Dom (fmap getName d))
            return scheme
          -- Unrefinable constructor
          _ -> return scheme
    -- Infer variable
    Nothing -> getVar v
-- Type literal
infer l@(Core.Lit _) = fromCoreScheme $ exprType l
-- Type application
infer (Core.App e1 (Core.Type e2)) = do
  t <- fromCore e2
  scheme <- infer e1
  case scheme of
    Forall (a : as) b ->
      return $ Forall as (subTyVar a t b)
    Mono Ambiguous -> return $ Mono Ambiguous
    _ -> pprPanic "Type is already saturated!" (ppr ())
-- Term application
infer (Core.App e1 e2) = infer e1 >>= \case
  Forall as Ambiguous -> Forall as Ambiguous <$ infer e2
  -- TODO: This should raise a warning for as /= []!
  Forall as (t3 :=> t4) -> do
    t2 <- mono <$> infer e2
    inferSubType t2 t3
    return $ Forall as t4
  _ -> pprPanic "Term application to non-function!" $ ppr (exprType e1, exprType e2)
infer (Core.Lam x e)
  | isTyVar x = do
    -- Type abstraction
    a <- getExternalName x
    infer e >>= \case
      Forall as t -> return $ Forall (a : as) t
  | otherwise = do
    -- Variable abstraction
    t1 <- fromCore $ varType x
    putVar (getName x) (Mono t1) (infer e) >>= \case
      Forall as t2 -> return $ Forall as (t1 :=> t2)
infer (Core.Let b e) = do
  ts <- inferRec b
  putVars ts $ infer e
infer (Core.Case e bind_e core_ret alts) = do
  -- Fresh return type
  ret <- fromCore core_ret
  -- Infer expression on which to pattern match
  t0 <- mono <$> infer e
  -- Add the variable under scrutinee to scope
  putVar (getName bind_e) (Mono t0) $
    case t0 of
      Data (Inj x d) as -> do
        ks <-
          mapMaybeM
            ( \case
                (Core.LitAlt l, _, _) -> pprPanic "Unexpected literal in datatype pattern!" (ppr l)
                (Core.DataAlt k, xs, rhs)
                  | not (exprIsBottom rhs) -> do
                    reach <- isBranchReachable e k
                    if reach
                      then do
                        -- Add constructor arguments introduced by the pattern
                        let ts = M.fromList $ zip (fmap getName xs) (Mono <$> dataConRefinedArgs x as k)
                        branchWithExpr e k (Inj x d) $ do
                          -- Ensure return type is valid
                          ret_i <- mono <$> putVars ts (infer rhs)
                          inferSubType ret_i ret
                        -- Record constructors
                        return (Just k)
                      else return Nothing
                _ -> return Nothing -- Skip defaults until all constructors have been seen
            )
            alts
        case findDefault alts of
          (_, Just rhs) | not (exprIsBottom rhs) ->
            -- Guard by unseen constructors
            branchAny e (tyConDataCons d L.\\ ks) (Inj x d) $
              do
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
              ts <- sequence $ M.fromList $ zip (fmap getName xs) (fmap (fromCoreScheme . varType) xs)
              -- Ensure return type is valid
              ret_i <- mono <$> putVars ts (infer rhs)
              inferSubType ret_i ret
          )
          alts
  return (Mono ret)
