{-# LANGUAGE LambdaCase #-}

module Intensional.InferCoreExpr
  ( inferProg,
  )
where

import Intensional.Ubiq
import Control.Monad.Extra
import Control.Monad.RWS.Strict
import Control.Monad.State.Strict as State
import CoreArity
import qualified CoreSyn as Core
import Data.Bifunctor
import qualified Data.IntSet as I
import qualified Data.List as L
import qualified Data.Map as M
import Intensional.FromCore
import GhcPlugins hiding ((<>), Type)
import Intensional.InferM
import Pair
import Intensional.Scheme as Scheme
import Intensional.Guard as Guard
import Intensional.Types

import qualified Intensional.Constraints as Constraints

import Debug.Trace

{-|
    The type of subtype inference constraints that are accumulated
    during the subtype inference fixpoint algorithm.

    There is a 1-1 correspondence between this type and the type of
    atomic constraints, but the former contain more information
    (though this information could be determined by the context at
    great expense).
-}
type SubTyAtom = (Guard, RVar, RVar, TyCon)

{-|
    The type of elements of the frontier in the subtype inference fixpoint
    algorithm.  There is an injection from this type into the typ of atomic
    constraints, but the inhabitants of this type additionally track the
    types used to instantiate the constructors of the datatype involved in
    the constraint.  This additional information is needed to unfold the 
    frontier and look for successors.
-}
type SubTyFrontierAtom = (Guard, RVar, RVar, TyCon, [Type], [Type])

{-|
    The type of the subtype inference algorithm, i.e. a stateful fixed 
    point computation that must additionally draw upon the services of 
    the inference monad to deal with GHC types.
-}
type SubTyComputation = StateT ([SubTyFrontierAtom], [SubTyAtom]) InferM ()

{-|
    Given a pair of types @t1@ and @t2@, @inferSubType t1 t2@ is the action
    that emits constraints characterising @t1 <= t2@.

    Also emits statistics on the size of the input parameters to do with slices.
-}
inferSubType :: Type -> Type -> InferM ()
inferSubType t1 t2 = 
  do  let ts = inferSubTypeStep t1 t2
      (_,cs) <- listen $
        forM_ ts $ \(x, y, d, as, as') ->
          do  -- Entering a slice
              ds <- snd <$> State.execStateT inferSubTypeFix ([(mempty, x, y, d, as, as')],[(mempty, x, y, d)])
              -- Note how big it was for statistics
              noteD $ length (L.nub $ map (\(_,_,_,d') -> getName d') ds)
              -- Emit a constraint for each one
              forM_ ds $ \(gs, x', y', d') -> 
                censor (Constraints.guardWith gs) (emitDD (Inj x' d') (Inj y' d'))
      when debugging $ 
        do  src <- asks inferLoc
            traceM ("[TRACE] Starting subtpe inference at " ++ traceSpan src)
            let sz = Constraints.size cs
            traceM ("[TRACE] The subtype proof at " ++ traceSpan src ++ " contributed " ++ show sz ++ " constraints.")

  where

    leq :: SubTyAtom -> SubTyAtom -> Bool
    leq (gs, x, y, d) (gs', x', y', d') =
      -- getName here is probably unnecessary, should look it up
      x == x' && y == y' && getName d == getName d' && gs' `Guard.impliedBy` gs
      
    inferSubTypeFix :: SubTyComputation
    inferSubTypeFix = 
      do  (frontier, acc) <-get
          unless (null frontier) $
            do  put ([], acc)
                forM_ frontier $ \(gs, x, y, d, as, as') -> 
                  do  let dataCons = tyConDataCons d
                      lift $ noteK (length dataCons)
                      forM_ dataCons $ \k -> 
                        do  xtys <- lift $ consInstArgs x as k
                            ytys <- lift $ consInstArgs y as' k
                            let gs' = 
                                 if (isTrivial d) 
                                   then gs 
                                   else Guard.singleton [getName k] x (getName d) <> gs
                            let ts  = concat $ zipWith inferSubTypeStep xtys ytys
                            forM_ ts $ \(x', y', d', bs, bs') ->
                              do  let new  = (gs', x', y', d')
                                  let newF = (gs', x', y', d', bs, bs')
                                  (fr, ac) <- get
                                  unless (any (`leq` new) ac) $ put (newF:fr, new:ac)
                inferSubTypeFix


    inferSubTypeStep ::  Type -> Type -> [(RVar, RVar, TyCon, [Type], [Type])]
    inferSubTypeStep (Data (Inj x d) as) (Data (Inj y _) as') =
      [(x, y, d, as, as')]
    inferSubTypeStep (t11 :=> t12) (t21 :=> t22) =
      let ds1 = inferSubTypeStep t21 t11 
          ds2 = inferSubTypeStep t12 t22
      in ds1 ++ ds2
    inferSubTypeStep (Data (Base _) as) (Data (Base _) as') =
      concat $ zipWith inferSubTypeStep as as'
    inferSubTypeStep _ _ = []

-- Infer constraints for a module
inferProg :: CoreProgram -> InferM Context
inferProg [] = return M.empty
inferProg (r : rs) =
  do  let bs = map occName $ bindersOf r 
      ctx <- if any isDerivedOccName bs then return mempty else associate r
      ctxs <- putVars ctx (inferProg rs)
      return (ctxs <> ctx)

-- Infer a set of constraints and associate them to qualified type scheme
associate :: CoreBind -> InferM Context
associate r = 
    setLoc (UnhelpfulSpan (mkFastString ("Top level " ++ bindingNames))) doAssoc
  where 
    bindingNames = 
      show $ map (occNameString . occName) (bindersOf r)
    doAssoc =
      do  when debugging $ traceM ("[TRACE] Begin inferring: " ++ bindingNames)
          env <- asks varEnv
          (ctx, cs) <- listen $ inferRec r
          let satAction s = 
                do  cs' <- snd <$> (listen $ saturate (do { tell cs; return s }))
                    -- Attempt to build a model and record counterexamples
                    es <- cexs cs'
                    return $ s { 
                        boundvs = (domain cs' <> domain s) I.\\ domain env,
                        Scheme.constraints = es <> cs'
                      }
          -- add constraints to every type in the recursive group
          ctx' <- mapM satAction ctx
          -- note down any counterexamples
          let es = M.foldl' (\ss sch -> Scheme.unsats sch <> ss) mempty ctx'
          noteErrs es
          when debugging $ traceM ("[TRACE] End inferring: " ++ bindingNames)  
          incrN      
          return ctx'

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
      Data dt as -> do
        ks <-
          mapMaybeM
            ( \case
                (Core.DataAlt k, xs, rhs)
                  | not (isBottoming rhs) -> do
                    -- Add constructor arguments introduced by the pattern
                    y <- fresh -- only used in Base case of ts
                    ts <- 
                      case dt of 
                        Inj x _ -> M.fromList . zip (fmap getName xs) <$> (map (Forall []) <$> (consInstArgs x as k))
                        Base _  -> M.fromList . zip (fmap getName xs) <$> (map (Forall []) <$> (consInstArgs y as k))
                    branchAny [k] dt $ do
                      -- Ensure return type is valid
                      ret_i <- mono <$> putVars ts (infer rhs)
                      inferSubType ret_i ret
                    -- Record constructorsc
                    return (Just k)
                (Core.LitAlt _, _, rhs) 
                  | not (isBottoming rhs) -> do
                        -- Ensure return type is valid
                        ret_i <- mono <$> infer rhs
                        inferSubType ret_i ret
                      -- Record constructors
                        return Nothing
                _ -> return Nothing -- Skip defaults until all constructors have been seen
            )
            alts
        case findDefault alts of
          (_, Just rhs) | not (isBottoming rhs) ->
            -- Guard by unseen constructors
            branchAny (tyConDataCons (tyconOf dt) L.\\ ks) dt $ do
              -- Ensure return type is valid
              ret_i <- mono <$> infer rhs
              inferSubType ret_i ret
          _ | (Inj x d) <- dt -> do
            -- Ensure destructor is total if not nested
            l <- asks inferLoc
            emitDK (Inj x d) ks l
          _ -> return ()
      _ -> 
        mapM_
            ( \(_, xs, rhs) ->
                  do -- Add constructor arguments introduced by the pattern
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
infer (Core.Tick SourceNote {sourceSpan = s} e) = setLoc (RealSrcSpan s) $ infer e -- Track location in source text
infer (Core.Tick _ e) = infer e -- Ignore other ticks
infer (Core.Coercion g) = freshCoreScheme (pSnd $ coercionKind g)
infer (Core.Type t) = pprPanic "Unexpected type" (ppr t)

isBottoming :: CoreExpr -> Bool
isBottoming e =
  case exprBotStrictness_maybe e of
    Nothing -> exprIsBottom e
    Just (_, _) -> True
