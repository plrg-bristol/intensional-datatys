module InferCoreExpr
    (
      inferProg
    ) where

import Types
import InferM
import GenericConGraph

import Control.Monad.RWS hiding (Sum)
import Control.Monad.Trans.Maybe
import qualified Data.Map as M

import qualified GhcPlugins as Core
import qualified PrimOp as Prim
import Kind

import Debug.Trace

data CaseAlt = Default | Literal [Core.Literal] | DataCon [(Core.DataCon, [Sort], [Type])] | Empty

-- Infer program
inferProg :: Core.CoreProgram -> InferM [(Core.Var, TypeScheme)]
inferProg p = do
  let xs = Core.bindersOfBinds p

  -- Add all module level definitions to context with an unconstrainted fresh type (t)
  ts <- mapM (freshScheme . toSortScheme .Core.exprType) (concatMap Core.rhssOfBind p)
  let m = M.fromList $ zip xs ts
  let withBinds = local (insertMany xs ts)

  -- Mut rec groups
  let groups = fmap (\b -> let xs = Core.bindersOf b in (xs, fmap (m M.!) xs, Core.rhssOfBind b)) p
  z <- mapM (\(xs, ts, rhss) -> do
    -- Infer each bind within the group
    binds <- mapM (withBinds . infer) rhss
    let (ts', cgs) = unzip binds

    -- Combine constraint graphs of group
    bcg <- foldM (\bcg' cg -> union bcg' cg `inExpr` ("Union", bcg', cg)) empty cgs

    -- Insure fresh types are quantified by infered constraint (t' < t) for recursion
    bcg' <- foldM (\bcg' (t', Forall as _ _ t) -> insert t' t bcg' `inExpr` ("Insert1", t', t, bcg')) bcg (zip ts' ts)

    -- Restrict constraints to the interface
    ts'' <- mapM (quantifyWith bcg') ts
    return (xs, ts'')
    ) groups
  return $ concatMap (uncurry zip) z

inferPoly :: Core.Var -> [Sort] -> Core.Expr Core.Var -> InferM (Type, ConGraph)
inferPoly x ts e =
  case Core.isDataConId_maybe x of
    Just k -> do
      -- Infer fully instantiated polymorphic constructor
      (d, as, args) <- safeCon k
      args' <- mapM fresh $ fmap (subSortVars as ts) args
      t  <- fresh $ SData d ts
      cg <- insert (K k ts args') t empty `inExpr` e
      return (foldr (:=>) t args', cg)
    Nothing -> 
      case Core.isPrimOpId_maybe x of
        Just p -> do
          -- Infer fully instaitated polymorphic primitive operator
          let (as, args, rt, _, _) = Prim.primOpSig p
          args' <- mapM fresh $ fmap (subSortVars as ts) $ fmap toSort args
          t  <- fresh $ toSort rt
          -- cg <- insert (K k ts args') t empty `inExpr` e
          return (foldr (:=>) t args', empty)
        Nothing ->  do
          -- Infer fully instantiated polymorphic variable
          (Forall as xs cs u) <- safeVar x
          if length as /= length ts
            then Core.pprPanic "Variables must fully instantiate type arguments." (Core.ppr x)
            else do
              -- Fresh refinement variables for local usage
              ys  <- mapM (fresh . \(RVar (_, _, d, ss)) -> SData d ss) xs
              ts' <- mapM fresh ts

              mcg <- runMaybeT $ fromList cs
              case mcg of
                Just cg -> do
                  -- Import x's constraints with local refinement variables
                  cg' <- foldM (\cg' (x, y) -> substitute y cg' x) (graphMap (subTypeVars as ts') cg) (zip xs ys) `inExpr` ("Sub", e)

                  -- Substitute type/ variables 
                  let u' = sub xs ys $ subTypeVars as ts' u
                  v <- fresh $ toSort $ Core.exprType e

                  cg'' <- insert u' v cg' `inExpr` ("Insert2", u', v, e)
                  return (v, cg'')

                Nothing -> error "Variable has inconsistent constriants."

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer e@(Core.Var x) =
  case Core.isDataConId_maybe x of
    Just k ->
      if isPrim k
        then do
          -- Infer literal constructor
          let (_, _, args, res) = Core.dataConSig k
          let (b, _) = Core.splitTyConApp res
          args' <- mapM (fresh . toSort) args
          return (foldr (:=>) (B b) args', empty)
        else do
          -- Infer monomorphic constructor
          (d, as, args) <- safeCon k
          if length as == 0
            then do
              ts <- mapM fresh args
              t  <- fresh $ SData d []
              cg <- insert (K k [] ts) t empty `inExpr` e
              return (foldr (:=>) t ts, cg)
            else
              Core.pprPanic "Constructors must be fully instantiated!" (Core.ppr ()) -- fromPoly should catch this
    Nothing -> do
      -- Infer monomorphic variable
      (t, cg) <- inferPoly x [] e
      return (t, cg)

infer l@(Core.Lit _) = do
  -- Infer literal expression
  t' <- fresh $ toSort $ Core.exprType l
  return (t', empty)

infer e@(Core.App e1 e2) =
  case fromPolyVar e of
    Just (x, ts) ->
      -- Infer polymorphic variable
      inferPoly x ts e
    Nothing -> do
      -- Infer application
      (t1, c1) <- infer e1
      (t2, c2) <- infer e2
      case t1 of
        t3 :=> t4 -> do
          cg <- union c1 c2 `inExpr` ("Union", c1, c2)
          cg' <- insert t2 t3 cg `inExpr` ("Insert3", t2, t3, e1)
          return (t4, cg')

infer e'@(Core.Lam x e) =
  if isLiftedTypeKind $ Core.varType x
    then
      -- Type abstraction
      infer e
    else do
      -- Variable abstraction
      t1 <- fresh $ toSort $ Core.varType x
      (t2, cg) <- local (insertVar x $ Forall [] [] [] t1) (infer e)
      return (t1 :=> t2, cg)

infer e'@(Core.Let b e) = do
  -- Infer local module (i.e. let expression)
  let xs = Core.bindersOf b
  let rhss = Core.rhssOfBind b

  -- Add each binds within the group to context with a fresh type (t) and no constraints
  ts <- mapM (freshScheme . toSortScheme . Core.exprType) rhss
  let withBinds = local (insertMany xs ts)

  (ts', cg) <- foldM (\(ts, cg) rhs -> do
    -- Infer each bind within the group, compiling constraints
    (t, cg') <- withBinds (infer rhs)
    cg'' <- union cg cg' `inExpr` rhs
    return (t:ts, cg'')
    ) ([], empty) rhss

  --  Insure fresh types are quantified by infered constraint (t' < t)
  cg' <- foldM (\cg (t', Forall as _ _ t) -> insert t' t cg) cg (zip ts' ts) `inExpr` e'

  -- Restrict constraints to the interface
  ts' <- mapM (quantifyWith cg') ts

  -- Infer in body
  (t, icg) <- local (insertMany xs ts') (infer e)
  cg'' <- union cg' icg `inExpr` e'
  return (t, cg'')

infer e'@(Core.Case e b rt as) = do
  -- Infer case expession
  let es = toSort $ Core.exprType e
  let mss = case es of {SData _ ss -> Just ss; _ -> Nothing}
  et <- fresh $ es
  t  <- fresh $ toSort rt
  (t0, c0) <- infer e
  c0' <- insert et t0 c0 `inExpr` e
  (caseType, cg) <- local (insertVar b $ Forall [] [] [] et) $ foldM (\(caseType, cg) a ->
    case a of
      -- Infer constructor alternative
      (Core.DataAlt d, bs, rhs) ->
        case mss of
          Just ss ->
            if Core.exprIsBottom rhs
              then
                -- Pass information to user about error
                return (caseType, cg)
              else do
                ts <- mapM (fresh . toSort . Core.varType) bs
                (ti', cgi) <- local (insertMany bs $ fmap (Forall [] [] []) ts) (infer rhs)
                cgi' <- insert ti' t cgi `inExpr` rhs
                cg' <- union cg cgi' `inExpr` rhs
                case caseType of
                  Empty     -> return (DataCon [(d, ss, ts)], cg')
                  DataCon s -> return (DataCon ((d, ss, ts):s), cg')
                  Default   -> return (Default, cg')
          Nothing -> Core.pprPanic "DataCon alt in non data con case!" (Core.ppr ())

      -- Infer literal alternative
      (Core.LitAlt l, _, rhs) -> do
        (ti', cgi) <- infer rhs
        cgi' <- insert ti' t cgi `inExpr` rhs
        cg' <- union cg cgi' `inExpr` rhs
        case caseType of
          Empty      -> return (Literal [l], cg')
          Literal s  -> return (Literal (l:s), cg')
          Default    -> return (Default, cg')

      -- Infer default alternative
      (Core.DEFAULT, _, rhs) ->
        if Core.exprIsBottom rhs
          then
            -- Pass information to user about error
            return (caseType, cg)
          else do
            (ti', cgi) <- infer rhs
            cgi' <- insert ti' t cgi `inExpr` rhs
            cg' <- union cg cgi' `inExpr` rhs
            return (Default, cg')
    ) (Empty, c0') as

  -- Insure destructor is total, GHC will conservatively insert defaults
  case caseType of
    Default -> return (t, cg)
    DataCon dts -> do
      cg' <- insert t0 (Sum [(TData dc ss, ts) | (dc, ss, ts) <- dts]) cg `inExpr` ("DataCon", t0, dts, cg, e')
      return (t, cg')
    Literal lss -> do
      cg' <- insert t0 (Sum [(TLit l, []) | l <- lss]) cg `inExpr` ("Literal", t0, e')
      return (t, cg')

-- Remove core ticks
infer (Core.Tick _ e) = infer e

-- Maintain constraints but give trivial type (Dot - a sub/super-type of everything) to expression - effectively ignore casts
-- GHC already requires the prog to well typed
infer (Core.Cast e c) = do
  (t, cg) <- infer e
  return (Dot, cg)

-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"