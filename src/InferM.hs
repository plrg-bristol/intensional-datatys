{-#  LANGUAGE MultiParamTypeClasses #-}

module InferM (
  InferM,
  InferME,
  inExpr,
  
  Context (Context, var),
  safeVar,
  safeCon,
  delta,
  insertVar,
  insertMany,
  
  fresh,
  freshScheme
) where

import Control.Monad.RWS

import Data.Functor.Identity
import qualified Data.Map as M

import qualified GhcPlugins as Core

import Types

-- The inference monad; a reader (i.e. local) context and a state (i.e. global) counter for taking fresh variables
type InferM = RWS Context () Int

-- Used to track the expression in which errors arrise
type InferME = RWS (Core.Expr Core.Var, Context) () Int

-- Attach an expression to an erroneous computation
inExpr :: InferME a -> Core.Expr Core.Var -> InferM a
inExpr ma e = withRWST (\ctx i -> ((e, ctx), i)) ma
  
-- The variables in scope and their type
newtype Context = Context {
  var :: M.Map Core.Var TypeScheme
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
safeCon :: Core.DataCon -> (Core.TyCon, [Core.Var], [Sort])
safeCon k = 
  let tc   = Core.dataConTyCon k
      as   = Core.dataConUnivAndExTyVars k
      args = toSort <$> Core.dataConOrigArgTys k -- Ignore evidence
  in (tc, as, args)

-- Extract polarised and instantiated constructor arguments from context
delta :: Bool -> Core.TyCon -> Core.DataCon -> [Sort] -> [PType]
delta p d k ss = 
  let (d', as, ts) = safeCon k
      ts' = subTypeVars as ss <$> ts
  in (polarise p <$> ts')

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