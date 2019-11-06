{-# LANGUAGE FlexibleInstances #-}

module InferCoreExpr
    (
      inferProg
    ) where

import Types
import InferM
import GenericConGraph

import Control.Monad.RWS hiding (Sum)
import Control.Monad.Trans.Maybe
import Control.Arrow
import Data.List hiding (union)
import Data.Maybe
import qualified Data.Map as M

import qualified GhcPlugins as Core
import qualified PrimOp as Prim
import Kind

import Debug.Trace

data CaseAlt = Default | Literal [Core.Literal] | DataCon [(Core.DataCon, [Sort], [Type])] | Empty

-- List all free variables of an expression
freeVars :: Core.Expr Core.Var -> [Core.Var]
freeVars (Core.Var i) = [i]
freeVars (Core.Lit l) = []
freeVars (Core.App e1 e2) = freeVars e1 ++ freeVars e2
freeVars (Core.Lam x e) = freeVars e \\ [x]
freeVars (Core.Let b e) = (freeVars e ++ concatMap freeVars (Core.rhssOfBind b)) \\ Core.bindersOf b
freeVars (Core.Case e x _ as) = freeVars e ++ (concat [freeVars ae \\ bs | (_, bs, ae) <- as] \\ [x])
freeVars (Core.Tick _ e) = freeVars e
freeVars (Core.Type t) = []
freeVars (Core.Coercion c) = []

instance Eq Core.CoreBind where
  b == b' = Core.bindersOf b == Core.bindersOf b'

-- Topological sort dependancies
toposort :: [(Core.CoreBind, [Core.CoreBind])] -> [Core.CoreBind]
toposort xs = foldl f [] [(x, y \\ [x]) | (x, y) <- xs]
  where
    f :: [Core.CoreBind] -> (Core.CoreBind, [Core.CoreBind]) -> [Core.CoreBind]
    f ts (x, xs) = nub $
      case elemIndex x ts of
        Just i -> uncurry (++) $ first (++ xs) $ splitAt i ts
        _      -> ts ++ xs ++ [x]

groupify :: [Core.Var] -> Core.CoreProgram -> [Core.CoreBind]
groupify xs p = mapMaybe f xs
  where
    f :: Core.Var -> Maybe Core.CoreBind
    f x = case [b | b <- p, x `elem` Core.bindersOf b] of {(h:_) -> Just h; _ -> Nothing}

-- Infer program
inferProg :: Core.CoreProgram -> InferM [(Core.Var, TypeScheme)]
inferProg p = do

  -- Reorder program with dependancies
  let defs = Core.bindersOfBinds p
  let deps = [(b, groupify ((concatMap freeVars . Core.rhssOfBind) b \\ Core.bindersOf b) p) | b <- p]
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
    bcg <- foldM (\bcg' cg -> union bcg' cg `inExpr` ("Union", bcg', cg)) empty cgs

    -- Insure fresh types are quantified by infered constraint (t' < t) for recursion
    -- Type/refinement variables bound in match those bound in t'
    bcg' <- foldM (\bcg' (t', Forall _ _ _ t) -> safeInsert t' t bcg') bcg (zip ts' ts)

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
      args' <- mapM (fresh . subSortVars as ts) args
      t  <- fresh $ SData d ts
      cg <- safeInsertExpr (K k ts args') t empty e
      return (foldr (:=>) t args', cg)
    Nothing ->
      case Core.isPrimOpId_maybe x of
        Just p -> do
          -- Infer fully instaitated polymorphic primitive operator
          let (as, args, rt, _, _) = Prim.primOpSig p
          args' <- mapM (fresh . subSortVars as ts . toSort) args
          t  <- fresh $ subSortVars as ts $ toSort rt
          return (foldr (:=>) t args', empty)
        Nothing -> do
          -- Infer fully instantiated polymorphic variable
          (Forall as xs cs u) <- safeVar x
          if length as /= length ts
            then Core.pprPanic "Variables must fully instantiate type arguments." (Core.ppr x)
            else do
              mcg <- runMaybeT $ fromList cs
              case mcg of
                Just cg -> do
                  -- Instantiate typescheme
                  ts' <- mapM fresh ts
                  let cg' = subConGraphTypeVars as ts' cg
                  let xs' = fmap (\(RVar (x, p, d, ss)) -> RVar (x, p, d, subSortVars as (broaden <$> ts') <$> ss)) xs
                  ys      <- mapM (fresh . \(RVar (_, _, d, ss)) -> SData d ss) xs'
                  let u'  = subTypeVars as ts' $ sub xs' ys u
                  
                  -- Import variables constraints at type
                  cg' <- foldM (\cg' (x, y) -> substitute y cg' x) cg' (zip xs' ys) `inExpr` ("Sub", e)

                  v <- fresh $ toSort $ Core.exprType e
                  cg'' <- safeInsertExpr u' v cg' e
                  return (v, cg'')

                Nothing -> error "Variable has inconsistent constriants."

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
          cg <- union c1 c2 `inExpr` ("Union", c1, c2)
          cg' <- safeInsertExpr t2 t3 cg e
          return (t4, cg')

infer e'@(Core.Lam x e) =
  if isLiftedTypeKind (Core.varType x) || Core.isDictId x
    then
      -- Type abstraction
      infer e
    else do
      -- Variable abstraction
      t1 <- fresh $ toSort $ Core.varType x
      (t2, cg) <- local (insertVar x $ Forall [] [] [] t1) (infer e)
      return (t1 :=> t2, cg)

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
    cg'' <- union cg cg' `inExpr` ("149", rhs)
    return (t:ts, cg'')
    ) ([], empty) rhss

  --  Insure fresh types are quantified by infered constraint (t' < t)
  cg' <- foldM (\cg (t', Forall as _ _ t) -> safeInsertExpr t' t cg e') cg (zip ts' ts)

  -- Restrict constraints to the interface
  ts' <- quantifyWith cg' ts

  -- Infer in body
  (t, icg) <- local (insertMany xs ts') (infer e)
  cg'' <- union cg' icg `inExpr` ("169", e')

  cg''' <- closeScope scope cg''
  return (t, cg''')

infer e'@(Core.Case e b rt as) = do
  scope <- get

  -- Infer case expession
  let es = toSort $ Core.exprType e
  let mss = case es of {SData _ ss -> Just ss; SBase _ ss -> Just ss; _ -> Nothing}
  et <- fresh es
  t  <- fresh $ toSort rt
  (t0, c0) <- infer e
  c0' <- safeInsertExpr et t0 c0 e
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
                cgi' <- safeInsertExpr ti' t cgi rhs
                cg' <- union cg cgi' `inExpr` ("186", rhs)
                case caseType of
                  Empty     -> return (DataCon [(d, ss, ts)], cg')
                  DataCon s -> return (DataCon ((d, ss, ts):s), cg')
                  Default   -> return (Default, cg')
          Nothing -> Core.pprPanic "DataCon alt in non data con case!" (Core.ppr ())

      -- Infer literal alternative
      (Core.LitAlt l, _, rhs) -> do
        (ti', cgi) <- infer rhs
        cgi' <- safeInsertExpr ti' t cgi rhs
        cg' <- union cg cgi' `inExpr` ("197", rhs)
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
            cgi' <- safeInsertExpr ti' t cgi rhs
            cg' <- union cg cgi' `inExpr` ("212", rhs)
            return (Default, cg')
    ) (Empty, c0') as

  -- Insure destructor is total, GHC will conservatively insert defaults
  cg <- case caseType of
    Default -> return cg
    DataCon dts -> safeInsertExpr t0 (Sum [(TData dc ss, ts) | (dc, ss, ts) <- dts]) cg e'
    Literal lss -> safeInsertExpr t0 (Sum [(TLit l, []) | l <- lss]) cg e'

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