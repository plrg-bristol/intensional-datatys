module InferM (
  InferM,
  Context (Context, var, con),
  safeVar,
  safeCon,
  delta,
  insertVar,
  insertMany,
  
  fresh,
  freshScheme
) where

import Control.Monad.RWS

import qualified Data.Map as M

import qualified GhcPlugins as Core

import Types

-- The inference monad; a reader (i.e. local) context and a state (i.e. global) counter for taking fresh variables
type InferM = RWS Context () Int

-- The variables (gamma) and constructors (delta) in scope
data Context = Context {
  var :: M.Map Core.Var TypeScheme,
  con :: Core.UniqFM {- Core.DataCon -} (Core.TyCon, [Core.Var], [Sort]) -- k -> (d, as, args)
}

-- Extract a variable from (local/global) context
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

-- Extract a constructor from (local/global) context
safeCon :: Core.DataCon -> InferM (Core.TyCon, [Core.Var], [Sort])
safeCon k = do
  ctx <- ask
  case Core.lookupUFM (con ctx) k of
    Just tcArgs -> return tcArgs
    Nothing   -> do
      -- We can assume the constructor is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined and have no existentially-quanitied type variables
      let tc   = Core.dataConTyCon k
      let as   = Core.dataConUnivTyVars k
      let args = toSort <$> Core.dataConOrigArgTys k
      return (tc, as, args)

-- Extract polarised and instantiated constructor arguments from context
delta :: Bool -> Core.TyCon -> Core.DataCon -> [Sort] -> InferM [PType]
delta p d k ss = do
  (d', as, ts) <- safeCon k
  let ts' = fmap (subTypeVars as ss) ts
  return $ fmap (polarise p) ts'

-- Insert a variable into the context
insertVar :: Core.Var -> TypeScheme -> Context ->  Context
insertVar x f ctx = ctx{var = M.insert x f $ var ctx}

-- Insert many variable into the context
insertMany :: [Core.Var] -> [TypeScheme] -> Context ->  Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (f:fs) ctx = insertVar x f $ insertMany xs fs ctx





-- A fresh refinement variable
fresh :: Sort -> InferM Type
fresh (SVar a)       = return $ TVar a
fresh (SBase b ss)   = return $ Base b ss
fresh s@(SData d ss)   = do
  i <- get
  put (i + 1)
  return $ upArrow i (polarise True s)
fresh (SArrow s1 s2) = do
  t1 <- fresh s1
  t2 <- fresh s2
  return (t1 :=> t2)
fresh (SApp s1 s2) = do
  t1 <- fresh s1
  return $ App t1 s2

-- A fresh refinement scheme for module/let bindings
freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as (SVar a))       = return $ Forall as [] [] $ TVar a
freshScheme (SForall as (SBase b ss))   = return $ Forall as [] [] $ Base b ss
freshScheme (SForall as s@(SData _ ss)) = do
  t <- fresh s
  case t of
    V x p d _ -> return $ Forall as [RVar (x, p, d, ss)] [] t
freshScheme (SForall as (SArrow s1 s2)) = do
  Forall _ v1 _ t1 <- freshScheme (SForall [] s1)
  Forall _ v2 _ t2 <- freshScheme (SForall [] s2)
  return $ Forall as (v1 ++ v2) [] (t1 :=> t2)
freshScheme (SForall as (SApp s1 s2)) = do
  t1 <- fresh s1
  return $ Forall as [] [] $ App t1 s2