{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, FlexibleContexts #-}

module InferM
    (
      InferM,
      Context (Context),
      con,
      var,
      inExpr,
      insertVar,
      insertMany,
      safeCon,
      closeScope,
      safeVar,
      fresh,
      freshScheme,
      quantifyWith
    ) where

import Types
import GenericConGraph

import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Control.Monad.RWS hiding (Sum)
import qualified Data.Map as M
import qualified Data.List as L

import qualified GhcPlugins as Core

import Debug.Trace

type InferM = RWS Context () Int

data Context = Context {
    con :: Core.UniqFM {- Core.DataCon -} (Core.TyCon, [Core.Var], [Sort]), -- k -> (d, args)
    var :: M.Map Core.Var TypeScheme
}

-- Last two constraint simplification rules
instance Rewrite RVar UType InferM where
  toNorm t1@(K k ss ts) t2@(V x p d ss') = do
      args <- delta p d k ss
      let ts' = upArrow x args
      if ts' /= ts
        then do
          c1 <- toNorm (K k ss ts') (V x p d ss')
          c2 <- toNorm (K k ss ts) (K k ss ts')
          return (c1 ++ c2)
        else return [(K k ss ts', V x p d ss'), (K k ss ts, K k ss ts')]
  toNorm t1@(V x p d ss) t2@(Sum cs) = do
      s <- mapM refineCon cs
      if cs /= s
        then do
          c1 <- toNorm (Sum s) (Sum cs)
          c2 <- toNorm (V x p d ss) (Sum s)
          return (c1 ++ c2)
        else return [(Sum s, Sum cs),(V x p d ss, Sum s)]
      where
        refineCon (TData k ss, ts) = do
          args <- delta p d k ss
          return (TData k ss, upArrow x args)
        refineCon t = return t
  toNorm t1 t2 = return [(t1, t2)]

-- closeScope scope1 scope2 cg var | Core.pprPanic "Close scope: " (Core.ppr (scope1, scope2, cg, ctxStems var)) False = undefined
closeScope scope1 scope2 cg var = purge (\(RVar (x, _, _, _)) -> scope2 > x && x > scope1 && (not (x `elem` ctxStems var))) cg
ctxStems m = concatMap (\(Forall _ ns cs t) -> [j | RVar (j, _, _, _) <- ns] ++ (concat $ concat [[stems c1, stems c2] | (c1, c2) <- cs]) ++ stems t) (M.elems m)

-- Handle constraint errors
inExpr :: Core.Outputable b => MaybeT InferM a -> b -> InferM a
inExpr ma e = do
  ma' <- runMaybeT ma
  case ma' of
    Just a -> return a
    Nothing  -> Core.pprPanic "Constraint conflict arrising from: " (Core.ppr e)

insertVar :: Core.Var -> TypeScheme -> Context ->  Context
insertVar x f ctx = ctx{var = M.insert x f $ var ctx}

insertMany :: [Core.Var] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (t:ts) ctx = insertVar x t (insertMany xs ts ctx)

safeVar :: Core.Var -> InferM TypeScheme
safeVar v = do
  ctx <- ask
  case var ctx M.!? v of
    Just ts -> return ts
    Nothing ->
      -- We can assume the variable is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let t = Core.varType v
      in freshScheme $ toSortScheme t

safeCon :: Core.DataCon -> InferM (Core.TyCon, [Core.Var], [Sort])
safeCon k = do
  ctx <- ask
  case Core.lookupUFM (con ctx) k of
    Just tcArgs -> return tcArgs
    Nothing   -> do
      -- We can assume the cosntructor is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let tc = Core.dataConTyCon k
      let as = Core.dataConUnivTyVars k -- asume there are no existentially-quanitied type variables
      let args = toSort <$> Core.dataConOrigArgTys k
      return (tc, as, args)

-- A fresh refinement variable
fresh :: Sort -> InferM Type
fresh t = do
  i <- get
  put (i + 1)
  return $ head $ upArrow i [polarise True t]

-- A fresh refinement scheme for module/let bindings
freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as (SVar a)) = return $ Forall as [] [] $ Con (TVar a) []
freshScheme (SForall as (SBase b ss)) = return $ Forall as [] [] $ Con (TBase b ss) []
freshScheme (SForall as s@(SData _ ss)) = do
  t <- fresh s
  case t of
    V x p d ss' | ss' == ss -> return $ Forall as [RVar (x, p, d, ss')] [] t -- Type arguments are perpendicular to refinement variables
    _ -> error "Fresh has gone wrong!"
freshScheme (SForall as (SArrow s1 s2)) = do
  Forall l1 v1 _ t1 <- freshScheme (SForall [] s1)  -- Fresh schemes have multiple refinement variables
  Forall l2 v2 _ t2 <- freshScheme (SForall [] s2)
  if length l1 + length l2 > 0
    then error "Rank 1 please."
    else return $ Forall as (v1 ++ v2) [] (t1 :=> t2)
-- freshScheme (SForall as (SApp s1 s2)) = return $ Forall as [] [] (Con (TApp s1 s2) [])
-- freshScheme (SForall as (SConApp tc args)) = return $ Forall as [] [] (Con (TConApp tc args) [])

-- Extract polarised and instantiated constructor arguments from context
delta :: Bool -> Core.TyCon -> Core.DataCon -> [Sort] -> InferM [PType]
delta p d k ss = do
  (d', as, ts) <- safeCon k
  let ts' = fmap (subSortVars as ss) ts
  if d == d'
    then return $ fmap (polarise p) ts'
    else Core.pprPanic "DataType doesn't contain constructor: " (Core.ppr (d, k))

-- Add restricted constraints to an unquantifed type scheme

quantifyWith :: ConGraph -> TypeScheme -> InferM TypeScheme
quantifyWith cg@ConGraph{succs = s, preds = p} t@(Forall as _ _ u) = do
   -- Take the full transitive closure of the graph using rewriting rules
   lcg <- saturate cg

   -- Check all the stems in the interface
   let chkStems = all (`elem` stems u) . stems

   -- Restricted congraph with chkStems
   let ns = L.nub $ [(t1, t2) | (t1, t2) <- lcg, t1 /= t2, chkStems t1, chkStems t2]

   -- Only quantified by refinement variables that appear in the inferface
   return $ Forall as (L.nub $ [x | (Var x, _) <- ns, (_, Var x) <- ns]) ns u
