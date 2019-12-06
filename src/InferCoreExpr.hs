{-# LANGUAGE ViewPatterns #-}

module InferCoreExpr (

) where

import Control.Monad.RWS hiding (Sum)
import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr
import qualified TyCon as Tc
import Constraint
import InferM

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer e@(Core.Var x) = inferVar x [] e -- Infer monomorphic variable

infer l@(Core.Lit _) = do
  -- Infer literal expression
  t' <- fresh $ toSort $ Core.exprType l
  return (t', emptyCG)

infer e@(Core.App e1 e2) =
  case fromPolyVar e of
    Just (x, ts) ->
      -- Infer polymorphic variable
      inferVar x ts e
    Nothing -> do
      -- Infer application
      (t1, c1) <- infer e1
      (t2, c2) <- infer e2
      case t1 of
        t3 :=> t4 -> do
          let cg = union c1 c2
          return (t4, emit t2 t3 (Just []) cg e)
        _ -> Core.pprPanic "Application to a non-function expression!" (Core.ppr (t1, e1))
  where
    -- Process a core type/evidence application
    fromPolyVar (Core.Var i) = Just (i, [])
    fromPolyVar (Core.App e1 (Core.Type t)) = do
      (i, ts) <- fromPolyVar e1
      return (i, ts ++ [toSort t])
    fromPolyVar (Core.App e1 e2) | Core.isPredTy (Core.exprType e2) = fromPolyVar e1 --For typeclass evidence
    fromPolyVar _ = Nothing

infer (Core.Lam x e) = do
  let t = Core.varType x
  if Core.isDictId x || isKind t -- Ignore typeclass evidence and type variable abstractions
    then infer e
    else do
      -- Variable abstraction
      t1 <- fresh $ toSort t
      (t2, cg) <- local (insertVar (Core.getName x) $ Forall [] [] [] t1) (infer e)
      return (t1 :=> t2, cg)
    where
      -- Does the type eventually return a lifted type kind
      isKind (Tcr.ForAllTy _ t) = isKind t
      isKind (Tcr.FunTy    _ t) = isKind t
      isKind (Tcr.AppTy t _)    = isKind t
      isKind (Tcr.TyConApp t _) = Tc.isKindTyCon t
      isKind t                  = isLiftedTypeKind t

infer e'@(Core.Let b e) = do
  -- Infer local module (i.e. let expression)
  let xs   = Core.getName <$> Core.bindersOf b
  let rhss = Core.rhssOfBind b

  -- Add each binds within the group to context with a fresh type (t) and no constraints
  ts <- mapM (freshScheme . toSortScheme . Core.exprType) rhss
  let withBinds = local (insertMany xs ts)

  (ts', cg) <- foldM (\(ts, cg) rhs -> do
    -- Infer each bind within the group, compiling constraints
    (t, cg') <- withBinds (infer rhs)
    return (ts ++ [t], union cg cg')
    ) ([], empty) rhss

  --  Insure fresh types are quantified by infered constraint (t' < t)
  let cg' = foldr (\(rhs, t', Forall _ _ t) cg-> emit t' t (Just []) cg rhs) cg (zip3 rhss ts' ts)

  -- Restrict constraints to the interface
  ts'' <- quantifyWith cg' ts

  -- Infer in body with infered typescheme to the environment
  (t, icg) <- local (insertMany xs ts'') (infer e)
  return (t, union cg' icg)

  -- Infer top-level case expession
infer e'@(Core.Case e b rt as) = do
  -- Fresh return type
  t  <- fresh $ toSort rt

  -- Infer expression on which to pattern match
  (t0, c0) <- infer e
  d <- case sort t0 of { SBase d _ -> d; SData d _ -> d }

  -- b @ e
  let es = toSort $ Core.exprType e
  et <- fresh es
  let c0' = emit et t0 (Just []) c0 e

  (caseType, cg) <- local (insertVar (Core.getName b) $ Forall [] [] [] et) (pushCase e >> foldM (\(caseType, cg) (a, bs, rhs) ->
    if Core.exprIsBottom rhs
      then return (caseType, cg) -- If rhs is bottom it is not a valid case
      else do
        -- Add variables introduced by the pattern
        ts <- mapM (fresh . toSort . Core.varType) bs

        -- Ensure return type is valid
        (ti', cgi) <- local (insertMany (Core.getName <$> bs) $ fmap (Forall [] [] []) ts) (infer rhs)
        let cgi' = emit ti' t (Just []) cgi e'

        -- Track the occurance of a constructors/default case
        case a of 
          Core.DataAlt (Core.getName -> k) -> return (fmap (\(t, as, k) -> (t, as, k)) caseType, union cg (guardWith k t0 cgi'))
          _                                -> return (Nothing, union cg cgi') -- Default/literal cases
    ) (Just (Nothing, Nothing, []), c0') as)

  popCase

  tl <- topLevel e

  -- Ensure destructor is total, GHC will conservatively insert defaults
  case caseType of
    Nothing  -> return (t, cg) -- Literal cases must have a default
    Just (Just tc, Just as, ks) -> 
      if tl 
        then return (t, emit t0 (Sum d ks as) (Just []) cg e')
        else return (t, cg)
    _ -> Core.pprPanic "Inconsistent data constructors arguments!" (Core.ppr ())

-- Remove core ticks
infer (Core.Tick _ e) = infer e

-- Maintain constraints but give trivial type (Dot - a sub/super-type of everything) to expression - effectively ignore casts
-- GHC already requires the prog to well typed
infer (Core.Cast e _) = do
  (_, cg) <- infer e
  return (Dot, cg)

-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"