{-# LANGUAGE FlexibleInstances, BangPatterns #-}

module InferCoreExpr
    (
      inferProg
    ) where

import Types
import InferM
import ConGraph

import Control.Monad.RWS hiding (Sum)
import Control.Monad.Trans.Maybe
import Control.Arrow
import Data.Maybe
import qualified Data.Map as M
import qualified Data.List as L

import qualified GhcPlugins as Core
import qualified TyCoRep as T
import qualified PrimOp as Prim
import Kind

import Debug.Trace

-- The type of a case expression
data CaseAlt = Default | Literal | DataCon [(Core.DataCon, [Sort], [Type])] | Empty

-- Process a core type/evidence application
fromPolyVar :: Core.CoreExpr -> Maybe (Core.Var, [Sort])
fromPolyVar (Core.Var i) = Just (i, [])
fromPolyVar (Core.App e1 (Core.Type t)) = do
  (i, ts) <- fromPolyVar e1
  return (i, ts ++ [toSort t])
fromPolyVar (Core.App e1 e2) | Core.isPredTy (Core.exprType e2) = fromPolyVar e1 --For typeclass evidence
fromPolyVar _ = Nothing

-- Topological sort dependancies
toposort :: [(Core.CoreBind, [Core.CoreBind])] -> [Core.CoreBind]
toposort xs = foldl f [] [(x, y L.\\ [x]) | (x, y) <- xs]
  where
    f :: [Core.CoreBind] -> (Core.CoreBind, [Core.CoreBind]) -> [Core.CoreBind]
    f ts (x, xs) = L.nub $
      case L.elemIndex x ts of
        Just i -> uncurry (++) $ first (++ xs) $ splitAt i ts
        _      -> ts ++ xs ++ [x]

-- List all free variables of an expression
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

-- Find the group which the variables are contained in
groupify :: [Core.Var] -> Core.CoreProgram -> [Core.CoreBind]
groupify xs p = mapMaybe f xs
  where
    f :: Core.Var -> Maybe Core.CoreBind
    f x = case [b | b <- p, x `elem` Core.bindersOf b] of {(h:_) -> Just h; _ -> Nothing}


-- Add restricted constraints to an unquantifed type scheme
quantifyWith :: ConGraph -> [TypeScheme] -> InferM [TypeScheme]
quantifyWith cg@ConGraph{succs = s, preds = p} ts = do
  -- Take the full transitive closure of the graph using rewriting rules
  lcg <- saturate cg

  -- Check all the stems in the interface
  let chkStems = all (\s -> any (\(Forall _ _ _ u) -> s `elem` stems u) ts) . stems

  -- Restricted congraph with chkStems
  let edges = L.nub [(t1, t2) | (t1, t2) <- lcg, t1 /= t2, chkStems t1, chkStems t2]

  -- Only quantified by refinement variables that appear in the inferface
  let nodes = L.nub ([x1 | (Var x1, _) <- edges] ++ [x2 | (_, Var x2) <- edges] ++ concat [vars u | Forall _ _ _ u <- ts])

  return $ [Forall as nodes edges u | Forall as _ _ u <- ts]

-- Infer program
inferProg :: Core.CoreProgram -> InferM [(Core.Var, TypeScheme)]
inferProg p = do

  -- Reorder program with dependancies
  let defs = Core.bindersOfBinds p
  let deps = [(b, groupify ((concatMap freeVars . Core.rhssOfBind) b L.\\ Core.bindersOf b) p) | b <- p]
  let p' = toposort deps

  -- Mut rec groups
  z <- foldr (\b r -> do
    let xs = Core.bindersOf b
    let rhss = Core.rhssOfBind b

    ts <- mapM (freshScheme . toSortScheme .Core.exprType) rhss
    let withBinds = local (insertMany xs ts)

    -- Infer each bind within the group
    binds <- mapM (withBinds . infer) rhss
    let (ts', cgs) = unzip binds

    -- Combine constraint graphs of group
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

inferPoly :: Core.Var -> [Sort] -> Core.Expr Core.Var -> InferM (Type, ConGraph)
inferPoly x ts e = do
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
              ts' <- mapM fresh ts
              let cg' = subTypeVars as ts' cg
              let xs' = fmap (\(RVar (x, p, d, ss)) -> RVar (x, p, d, subTypeVars as ts <$> ss)) xs
              ys      <- mapM (fresh . \(RVar (_, _, d, ss)) -> SData d ss) xs'
              let u'  = subTypeVars as ts' $ subRefinementVars xs' ys u
              
              -- Import variables constraints at type
              cg'' <- foldM (\cg' (x, y) -> substitute x y cg') cg' (zip xs' ys)

              v <- fresh $ toSort $ Core.exprType e
              cg''' <- insert u' v cg''
              return (v, cg''')

  cg' <- closeScope scope cg
  return (t, cg')

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer e@(Core.Var x) = inferPoly x [] e

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
          cg <- union c1 c2
          cg' <- insert t2 t3 cg
          return (t4, cg')
        _ ->  Core.pprPanic "case" (Core.ppr e1)

infer e'@(Core.Lam x e) =
  if isKind (Core.varType x) || Core.isDictId x
    then
      -- Type abstraction
      infer e
    else do
      -- Variable abstraction
      t1 <- fresh $ toSort $ Core.varType x
      (t2, cg) <- local (insertVar x $ Forall [] [] [] t1) (infer e)
      return (t1 :=> t2, cg)
    where
      isKind (T.FunTy t1 t2) = isLiftedTypeKind t2
      isKind t = isLiftedTypeKind t || Core.isPredTy t

infer e'@(Core.Let b e) = do
  scope <- get

  -- Infer local module (i.e. let expression)
  let xs = Core.bindersOf b
  let rhss = Core.rhssOfBind b

  -- Add each binds within the group to context with a fresh type (t) and no constraints
  ts <- mapM (freshScheme . toSortScheme . Core.exprType) rhss
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
  ts' <- quantifyWith cg' ts

  -- Infer in body with infered typescheme to the environment
  (t, icg) <- local (insertMany xs ts') (infer e)
  cg'' <- union cg' icg

  cg''' <- closeScope scope cg''
  return (t, cg''')

  -- Infer case expession
infer e'@(Core.Case e b rt as) = do
  scope <- get

  -- Fresh return type
  t  <- fresh $ toSort rt

  -- Infer expression to pattern match on
  let es = toSort $ Core.exprType e
  let mss = case es of {SData _ ss -> Just ss; _ -> Nothing}
  et <- fresh es
  (t0, c0) <- infer e
  c0' <- insert et t0 c0

  (caseType, cg) <- local (insertVar b $ Forall [] [] [] et) $ foldM (\(caseType, cg) a ->
    case a of
      -- Infer constructor alternative
      (Core.DataAlt d, bs, rhs) ->
        case mss of
          Just ss ->
            if Core.exprIsBottom rhs -- If rhs is bottom it is not a valid case
              then return (caseType, cg)
              else do
                -- Add variables introduced by the pattern
                ts <- mapM (fresh . toSort . Core.varType) bs

                -- Ensure return type is valid
                (ti', cgi) <- local (insertMany bs $ fmap (Forall [] [] []) ts) (infer rhs)
                cgi' <- insert ti' t cgi
                cg' <- union cg cgi'
                case caseType of
                  Empty     -> return (DataCon [(d, ss, ts)], cg')
                  DataCon s -> return (DataCon ((d, ss, ts):s), cg')
                  Default   -> return (Default, cg')
          Nothing -> Core.pprPanic "DataCon alt in non data con case!" (Core.ppr ())

      -- Infer literal alternative
      (Core.LitAlt l, _, rhs) -> do
        -- Ensure return type is valid
        (ti', cgi) <- infer rhs
        cgi' <- insert ti' t cgi
        cg' <- union cg cgi'
        case caseType of
          Empty   -> return (Literal, cg')
          Literal -> return (Literal, cg')
          Default -> return (Default, cg')

      -- Infer default alternative
      (Core.DEFAULT, _, rhs) ->
        if Core.exprIsBottom rhs -- If rhs is bottom it is not a valid case
          then return (caseType, cg)
          else do
            -- Ensure return type is valid
            (ti', cgi) <- infer rhs
            cgi' <- insert ti' t cgi
            cg' <- union cg cgi'
            return (Default, cg')
    ) (Empty, c0') as

  -- Insure destructor is total, GHC will conservatively insert defaults
  cg <- case caseType of
    Default     -> return cg
    DataCon dts -> insert t0 (Sum [(dc, ss, ts) | (dc, ss, ts) <- dts]) cg
    Literal     -> Core.pprPanic "Literal cases require default!" (Core.ppr ())

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