{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

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
    con :: Core.UniqFM {- Core.DataCon -} (Core.TyCon, [Sort]), -- k -> (d, args)
    var :: M.Map Core.Var TypeScheme
}

-- Last two constraint simplification rules
instance Rewrite RVar UType InferM where
  toNorm t1@(K k ts) t2@(V x p d) = do
      args <- delta p d k
      let ts' = upArrow x args
      if ts' /= ts
        then do
          c1 <- toNorm (K k ts') (V x p d)
          c2 <- toNorm (K k ts) (K k ts')
          return (c1 ++ c2)
        else return [(K k ts', V x p d), (K k ts, K k ts')]
  toNorm t1@(V x p d) t2@(Sum cs) = do
      s <- mapM refineCon cs
      if cs /= s
        then do
          c1 <- toNorm (Sum s) (Sum cs)
          c2 <- toNorm (V x p d) (Sum s)
          return (c1 ++ c2)
        else return [(Sum s, Sum cs),(V x p d, Sum s)]
      where
        refineCon (TData k, ts) = do
          args <- delta p d k
          return (TData k, upArrow x args)
  toNorm t1 t2 = return [(t1, t2)]

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
    Nothing -> do
      -- We can assume the variable is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let t = Core.varType v
      t' <- freshScheme $ toSortScheme t
      return t'

safeCon :: Core.DataCon -> InferM (Core.TyCon, [Sort])
safeCon k = do
  ctx <- ask
  case Core.lookupUFM (con ctx) k of
    Just tcArgs -> return tcArgs
    Nothing   -> do
      -- We can assume the cosntructor is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let tc = Core.dataConTyCon k
      let args = toSort <$> Core.dataConOrigArgTys k
      return (tc, args)

-- A fresh refinement variable
fresh :: Sort -> InferM Type
fresh t = do
  i <- get
  put (i + 1)
  return $ head $ upArrow i [polarise True t]

-- A fresh refinement scheme for module/let bindings
freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as (SVar a)) = return $ Forall as [] [] $ Con (TVar a) []
freshScheme (SForall as (SBase b)) = return $ Forall as [] [] $ Con (TBase b) []
freshScheme (SForall as s@(SData _)) = do
  t <- fresh s
  case t of
    V x p d -> return $ Forall as [RVar (x, p, d)] [] t
    _ -> error "Fresh has gone wrong!"
freshScheme (SForall as (SArrow s1 s2)) = do
  Forall l1 v1 _ t1 <- freshScheme (SForall [] s1)  -- Fresh schemes have multiple refinement variables
  Forall l2 v2 _ t2 <- freshScheme (SForall [] s2)
  if length l1 + length l2 > 0
    then error "Rank 1 please."
    else return $ Forall as (v1 ++ v2) [] (t1 :=> t2)
freshScheme (SForall as (SApp s1 s2)) = return $ Forall as [] [] (Con (TApp s1 s2) [])
freshScheme (SForall as (SConApp tc args)) = return $ Forall as [] [] (Con (TConApp tc args) [])

-- Extract polarised constructor arguments from context
delta :: Bool -> Core.TyCon -> Core.DataCon -> InferM [PType]
delta p d k = do
  (d', ts) <- safeCon k
  if d == d'
    then return $ fmap (polarise p) ts
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
   return $ Forall as [x | (Var x, _) <- ns, (_, Var x) <- ns] ns u
