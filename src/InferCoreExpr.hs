{-# LANGUAGE FlexibleInstances, BangPatterns #-}

module InferCoreExpr
    (
      inferProg
    ) where

import Control.Monad.RWS hiding (Sum)
import Control.Arrow

import Data.Maybe
import qualified Data.List as L

import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr
import qualified TyCon as Tc
import qualified PrimOp as Prim
import Kind

import Types
import InferM
import ConGraph

-- Add restricted constraints to an unquantifed type scheme
quantifyWith :: ConGraph -> [TypeScheme] -> InferM [TypeScheme]
quantifyWith cg@ConGraph{succs = s, preds = p, subs = sb} ts = do

  -- Rewrite ts using equivalence class representations
  let ts' = [Forall as [] [] (subRefinementMap sb u) | Forall as _ [] u <- ts]

  -- Take the full transitive closure of the graph using rewriting rules
  lcg <- saturate cg

  -- Check all the stems in the interface
  let chkStems = all (\s -> any (\(Forall _ _ _ u) -> s `elem` (stems u)) ts') . stems

  -- Restricted congraph with chkStems
  let edges = L.nub [(t1, t2) | (t1, t2) <- lcg, t1 /= t2, chkStems t1, chkStems t2]

  -- Only quantified by refinement variables that appear in the inferface
  let nodes = L.nub ([x1 | (Var x1, _) <- edges] ++ [x2 | (_, Var x2) <- edges] ++ concat [vars u | Forall _ _ _ u <- ts'])

  return [Forall as nodes edges u | Forall as _ _ u <- ts']





-- List all free variables in an expression
freeVars :: Core.Expr Core.Var -> [Core.Var]
freeVars (Core.Var i) = [i]
freeVars (Core.Lit l) = []
freeVars (Core.App e1 e2) = freeVars e1 ++ freeVars e2
freeVars (Core.Lam x e) = freeVars e L.\\ [x]
freeVars (Core.Let b e) = (freeVars e ++ concatMap freeVars (Core.rhssOfBind b)) L.\\ Core.bindersOf b
freeVars (Core.Case e x _ as) = freeVars e ++ (concat [freeVars ae L.\\ bs | (_, bs, ae) <- as] L.\\ [x])
freeVars (Core.Cast e _) = freeVars e
freeVars (Core.Tick _ e) = freeVars e
freeVars (Core.Type t) = []
freeVars (Core.Coercion c) = []

-- Used to compare groups
instance Eq Core.CoreBind where
  b == b' = Core.bindersOf b == Core.bindersOf b'

-- Sort a program in order of dependancies
dependancySort :: Core.CoreProgram -> Core.CoreProgram
dependancySort p = foldl go [] depGraph
  where
    -- Pair binder groups with their dependancies
    depGraph = [(b, [group | rhs <- Core.rhssOfBind b, fv <- freeVars rhs, group <- findGroup p fv, group /= b]) | b <- p]

    go p' (b, deps) = L.nub $
      case L.elemIndex b p' of
        Just i -> uncurry (++) $ first (++ deps) $ splitAt i p' -- Insert dependencies before binder
        _      -> p' ++ deps ++ [b]                             -- Concatenate dependencies and binder to the end of the program
    
    -- Find the group in which the variable is contained
    findGroup [] x = []
    findGroup (b:bs) x
      | x `elem` Core.bindersOf b = [b]
      | otherwise = findGroup bs x




      
-- Infer program
inferProg :: Core.CoreProgram -> InferM [(Core.Var, TypeScheme)]
inferProg p = do

  -- Reorder program with dependancies
  let p' = dependancySort p

  -- Mut rec groups
  z <- foldr (\b r -> do
    let xs   = Core.bindersOf b
    let rhss = Core.rhssOfBind b

    -- Fresh typescheme for each binder in the group
    ts <- mapM (freshScheme . toSortScheme . Core.exprType) rhss

    -- Infer constraints for the rhs of each bind
    binds <- mapM (local (insertMany xs ts) . infer) rhss
    let (ts', cgs) = unzip binds

    -- Combine constraint graphs
    bcg <- foldM union empty cgs

    -- Insure fresh types are quantified by infered constraint (t' < t) for recursion
    -- Type/refinement variables bound in match those bound in t'
    bcg' <- foldM (\bcg' (t', Forall _ _ _ t) -> insert t' t bcg') bcg (zip ts' ts)
    
    -- Restrict constraints to the interface
    ts'' <- quantifyWith bcg' ts

    -- Add infered typescheme to the environment
    r' <- local (insertMany xs ts'') r
    return $ (xs, ts''):r'
    ) (return []) p'
  return $ concatMap (uncurry zip) z





-- Infer a fully polyorphic variable with fully instantiated type arguments
inferVar :: Core.Var -> [Sort] -> Core.Expr Core.Var -> InferM (Type, ConGraph)
inferVar x ts e = do
  scope <- get

  (t, cg) <- case Core.isDataConId_maybe x of
    Just k -> do
      -- Infer fully instantiated polymorphic constructor
      (d, as, args) <- safeCon k
      args' <- mapM (fresh . subTypeVars as ts) args
      t  <- fresh $ SData d ts
      cg <- insert (Con k ts args') t empty
      return (foldr (:=>) t args', cg)

    Nothing ->
      case Core.isPrimOpId_maybe x of
        Just p -> do
          -- Infer fully instaitated polymorphic primitive operator
          let (as, args, rt, _, _) = Prim.primOpSig p
          args' <- mapM (fresh . subTypeVars as ts . toSort) args
          t  <- fresh $ subTypeVars as ts $ toSort rt
          return (foldr (:=>) t args', empty)

        Nothing -> do
          -- Infer fully instantiated polymorphic variable
          (Forall as xs cs u) <- safeVar x
          cg <- fromList cs
          if length as /= length ts
            then Core.pprPanic "Variables must fully instantiate type arguments." (Core.ppr x)
            else do
              -- Instantiate typescheme
              ts'     <- mapM fresh ts
              let cg' =  subTypeVars as ts' cg
              let xs' =  fmap (\(RVar (x, p, d, ss)) -> RVar (x, p, d, subTypeVars as ts <$> ss)) xs
              ys      <- mapM (fresh . \(RVar (_, _, d, ss)) -> SData d ss) xs'
              let u'  =  subTypeVars as ts' $ subRefinementVars xs' ys u
              
              -- Import variables constraints at type
              cg'' <- foldM (\cg' (x, y) -> substitute x y cg') cg' (zip xs' ys)

              v <- fresh $ toSort $ Core.exprType e
              cg''' <- insert u' v cg''
              return (v, cg''')

  cg' <- closeScope scope cg
  return (t, cg')

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer e@(Core.Var x) = inferVar x [] e -- Infer monomorphic variable

infer l@(Core.Lit _) = do
  -- Infer literal expression
  t' <- fresh $ toSort $ Core.exprType l
  return (t', empty)

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
          cg  <- union c1 c2
          cg' <- insert t2 t3 cg
          return (t4, cg')
  where
    -- Process a core type/evidence application
    fromPolyVar (Core.Var i) = Just (i, [])
    fromPolyVar (Core.App e1 (Core.Type t)) = do
      (i, ts) <- fromPolyVar e1
      return (i, ts ++ [toSort t])
    fromPolyVar (Core.App e1 e2) | Core.isPredTy (Core.exprType e2) = fromPolyVar e1 --For typeclass evidence
    fromPolyVar _ = Nothing

infer e'@(Core.Lam x e) = do
  let t = Core.varType x
  if Core.isDictId x || isKind t -- Ignore typeclass evidence and type variable abstractions
    then infer e
    else do
      -- Variable abstraction
      t1 <- fresh $ toSort t
      (t2, cg) <- local (insertVar x $ Forall [] [] [] t1) (infer e)
      return (t1 :=> t2, cg)
    where
      -- Does the type eventually return a lifted type kind
      isKind (Tcr.ForAllTy _ t) = isKind t
      isKind (Tcr.FunTy    _ t) = isKind t
      isKind (Tcr.AppTy t _)    = isKind t
      isKind (Tcr.TyConApp t _) = Tc.isKindTyCon t
      isKind t                  = isLiftedTypeKind t

infer e'@(Core.Let b e) = do
  scope <- get

  -- Infer local module (i.e. let expression)
  let xs   = Core.bindersOf b
  let rhss = Core.rhssOfBind b

  -- Add each binds within the group to context with a fresh type (t) and no constraints
  ts <- mapM (freshScheme . toSortScheme . Core.exprType) rhss
  let withBinds = local (insertMany xs ts)

  (ts', cg) <- foldM (\(ts, cg) rhs -> do
    -- Infer each bind within the group, compiling constraints
    (t, cg') <- withBinds (infer rhs)
    cg''     <- union cg cg'
    return (t:ts, cg'')
    ) ([], empty) rhss

  --  Insure fresh types are quantified by infered constraint (t' < t)
  cg' <- foldM (\cg (t', Forall as _ _ t) -> insert t' t cg) cg (zip ts' ts)

  -- Restrict constraints to the interface
  ts' <- quantifyWith cg' ts

  -- Infer in body with infered typescheme to the environment
  (t, icg) <- local (insertMany xs ts') (infer e)
  cg''     <- union cg' icg

  cg''' <- closeScope scope cg''
  return (t, cg''')

  -- Infer case expession
infer e'@(Core.Case e b rt as) = do
  scope <- get

  -- Fresh return type
  t  <- fresh $ toSort rt

  -- Infer expression to pattern match on
  let es = toSort $ Core.exprType e
  et <- fresh es
  (t0, c0) <- infer e
  c0' <- insert et t0 c0

  (caseType, cg) <- local (insertVar b $ Forall [] [] [] et) $ foldM (\(caseType, cg) (a, bs, rhs) ->
    if Core.exprIsBottom rhs
      then return (caseType, cg) -- If rhs is bottom it is not a valid case
      else do
        -- Add variables introduced by the pattern
        ts <- mapM (fresh . toSort . Core.varType) bs

        -- Ensure return type is valid
        (ti', cgi) <- local (insertMany bs $ fmap (Forall [] [] []) ts) (infer rhs)
        cgi'       <- insert ti' t cgi
        cg'        <- union cg cgi'

        -- Track the occurance of a constructors/default case
        caseType' <- case a of
          Core.DataAlt d -> case caseType of
            Just s  -> let SData _ ss = es in return $ Just ((d, ss, ts):s)
            Nothing -> return Nothing
          _         -> return Nothing
        
        return (caseType', cg')
    ) (Just [], c0') as

  -- Insure destructor is total, GHC will conservatively insert defaults
  cg <- case caseType of
    Nothing  -> return cg -- Literal cases must have a default
    Just dts -> insert t0 (Sum [(dc, ss, ts) | (dc, ss, ts) <- dts]) cg

  cg' <- closeScope scope cg
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