module InferCoreExpr
    (
      inferProg
    ) where

import Utils
import Types
import Errors
import InferM
import GenericConGraph
import Control.Monad.Except
import Control.Monad.RWS hiding (Sum)
import qualified Data.List as L
import qualified Data.Map as M
import qualified GhcPlugins as Core
import qualified CoreUtils as Utils
import Demand
import Debug.Trace
import CoreArity

data CaseAlt = Default | Literal [Core.Literal] | DataCon [(Core.DataCon, [Type])] | Empty

-- -- Add restricted constraints to an unquantifed type scheme
quantifyWith :: ConGraph -> TypeScheme -> InferM TypeScheme
quantifyWith cg@ConGraph{succs = s, preds = p} t@(Forall as [] _ u) = do

  -- Take the full transitive closure of the graph using rewriting rules
  lcg <- saturate cg

  -- Are all the stems in the interface?
  let chkStems = all (`elem` stems u) . stems

  -- Restricted congraph
  let ns = L.nub $ [(t1, t2) | (t1, t2) <- lcg, t1 /= t2, chkStems t1, chkStems t2]
  cg' <- fromList ns

  -- Only quantified by refinement variables that appear in the inferface
  return $ Forall as [x | Var x <- nodes cg'] cg' u
quantifyWith _ _ = error "Cannot restrict refinement quantified type."

-- Infer program
inferProg :: Core.CoreProgram -> InferM [(Core.Var, TypeScheme)]
inferProg p = do
  let xs = Core.bindersOfBinds p

  -- Add all module level definitions to context with a fresh type (t) and no constraints
  ts <- mapM (freshScheme . toSortScheme . Core.varType) xs
  let m = M.fromList $ zip xs ts
  let withBinds = local (insertMany xs ts)

  z <- mapM (\(xs, ts, rhss) -> do
    -- Infer a binder group
    (ts', bcg) <- foldM (\(ts, cg) rhs -> do
        -- Infer each bind within the group, compiling constraints
        (t, cg') <- withBinds (infer rhs)
        cg'' <- union cg cg'
        return (t:ts, cg'')
        ) ([], empty) rhss

    -- Insure fresh types are quantified by infered constraint (t' < t) for recursion
    bcg' <- foldM (\bcg' (t', Forall as _ _ t) ->  insert t' t bcg') bcg (zip ts' ts)

    -- Restrict constraints to the interface
    ts' <- mapM (quantifyWith bcg') ts
    return (xs, ts')

    ) $ fmap (\b -> let xs = Core.bindersOf b in (xs, fmap (m M.!) xs, Core.rhssOfBind b)) p
  return $ concatMap (uncurry zip) z

-- Infer fully instantiated polymorphic variable
inferVar :: Core.Var -> [Sort] -> InferM (Type, ConGraph)
inferVar x ts = do
  (Forall as xs cg u) <- safeVar x
  if length as /= length ts
    then throwError $ PolyTypeError x
    else do
      ys  <- mapM fresh $ map (\(RVar (x, p, d)) -> SData d) xs
      ts' <- mapM fresh ts
      v   <- fresh $ toSort $ Core.varType x
      cg' <- insert (sub xs ys u) v cg
      cg'' <- foldM (\cg (x, se) -> substitute se cg x) cg' (zip xs ys)
      return $ (v, graphMap (subTypeVars as ts') cg'')

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer e'@(Core.Var x) =
  case isConstructor x of
    Just k -> do
      if isPrim k
        then do
          -- Infer literal cosntructor
          let (_, _, args, res) = Core.dataConSig k
          let (b, _) = Core.splitTyConApp res
          args' <- mapM (fresh . toSort) args
          return (foldr (:=>) (B b) args', empty)
        else do
          -- Infer constructor
          (d, args) <- safeCon k `throwInExpr` e'
          ts <- mapM fresh args
          t  <- fresh $ SData d
          cg <- insert (K k ts) t empty
          return (foldr (:=>) t ts, cg)
    Nothing ->
      -- Infer monomorphic variable
      inferVar x []

infer l@(Core.Lit _) = do
  -- Infer literal expression
  t' <- fresh $ toSort $ Utils.exprType l
  return (t', empty)

infer e@(Core.App e1 e2) =
  case fromPolyVar e of
    Just (x, ts) -> do
      -- Infer polymorphic variable
      inferVar x ts
    otherwise -> do
      -- Infer application
      (t1, c1) <- infer e1 `throwInExpr` e
      (t2, c2) <- infer e2 `throwInExpr` e
      case t1 of
        t3 :=> t4 -> do
          cg <- union c1 c2
          cg' <- insert t2 t3 cg
          return (t4, cg')

infer e'@(Core.Lam x e) = do
  -- Infer abstraction
  t1 <- fresh $ toSort $ Core.varType x
  (t2, cg) <- local (insertVar x $ Forall [] [] empty t1) (infer e `throwInExpr` e')
  return (t1 :=> t2, cg)

infer (Core.Let b e) = do
  -- Infer local module (i.e. let expression)
  let xs = Core.bindersOf b
  let rhss = Core.rhssOfBind b

  -- Add each binds within the group to context with a fresh type (t) and no constraints
  ts <- mapM (freshScheme . toSortScheme . Core.varType) xs
  let withBinds = local (insertMany xs ts)

  (ts', cg) <- foldM (\(ts, cg) rhs -> do
    -- Infer each bind within the group, compiling constraints
    (t, cg') <- withBinds (infer rhs)
    cg'' <- union cg cg'
    return (t:ts, cg'')
    ) ([], empty) rhss

  --  Insure fresh types are quantified by infered constraint (t' < t)
  cg' <- foldM (\cg (t', Forall as _ _ t) -> insert t' t cg) cg (zip ts' ts)

  -- Restrict constraints to the interface
  ts' <- mapM (quantifyWith cg') ts

  -- Infer in body
  (t, icg) <- withBinds (infer e)
  cg'' <- cg' `union` icg
  return (t, cg')

infer (Core.Case e b rt as) = do
  -- Infer case expession
  et <- fresh $ toSort $ Utils.exprType e
  t  <- fresh $ toSort rt
  (t0, c0) <- infer e `throwInExpr` e
  c0' <- insert et t0 c0 `throwInExpr` e
  (caseType, cg)  <- local (insertVar b $ Forall [] [] empty et) $ foldM (\(caseType, cg) a ->
    case a of
      -- Infer constructor alternative
      (Core.DataAlt d, bs, rhs) ->
        -- Check if rhs is bottom
          if Utils.exprIsBottom rhs
            then do
              -- Pass information to user about error
              return (caseType, cg)
            else do
              ts <- mapM (fresh . toSort . Core.varType) bs
              (ti', cgi) <- local (insertMany bs $ fmap (Forall [] [] empty) ts) (infer rhs)
              cgi' <- insert ti' t cgi
              cg' <- cg `union` cgi'
              case caseType of
                Empty     -> return (DataCon [(d, ts)], cg')
                DataCon s -> return (DataCon ((d, ts):s), cg')
                Default   -> return (Default, cg')

      -- Infer literal alternative
      (Core.LitAlt l, [], rhs) -> do
        (ti', cgi) <- infer rhs
        cgi' <- insert ti' t cgi
        cg' <- cg `union` cgi'
        case caseType of
          Empty      -> return (Literal [l], cg')
          Literal s  -> return (Literal (l:s), cg')
          Default    -> return (Default, cg')

      -- Infer default alternative
      (Core.DEFAULT, [], rhs) -> do
        if Utils.exprIsBottom rhs
          then do
            -- Pass information to user about error
            return (caseType, cg)
          else do
            (ti', cgi) <- infer rhs
            cgi' <- insert ti' t cgi
            cg' <- cg `union` cgi'
            return (Default, cg')
    ) (Empty, c0') as `throwInExpr` e

  -- Insure destructor is total
  case caseType of
    Default -> return (t, cg)
    DataCon dts -> do
      cg' <- insert t0 (Sum [(TData dc, ts) | (dc, ts) <- dts]) cg  `throwInExpr` e
      return (t, cg')
    Literal lss -> do
      cg' <- insert t0 (Sum [(TLit l, []) | l <- lss]) cg  `throwInExpr` e
      return (t, cg')

-- Remove core ticks
infer (Core.Tick t e) = infer e

infer _ = error "Unimplemented"
