{-#  LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module InferM (
  InferM,
  pushCase,
  popCase,
  topLevel,
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

import qualified Data.Map as M

import IfaceType
import ToIface
import qualified GhcPlugins as Core

import Types

-- The inference monad; a reader (i.e. local) context and a state (i.e. global) counter for taking fresh variables
-- A stack of a names which have pattern matched to corrctly order nested case
type InferM = RWST Context () ([Core.Expr Core.Var], Int) IO

-- TODO: better comparison for top-level
instance Eq (Core.Expr Core.Var) where
  Core.Var i == Core.Var i' = Core.getUnique i == Core.getUnique i'
  _ == _ = False

-- Enter a new case statement
pushCase :: Core.Expr Core.Var-> InferM ()
pushCase c = modify (\(cs, i) -> (c:cs, i))

-- Exit a case statement
popCase :: InferM ()
popCase = modify (\(c:cs, i) -> (cs, i))

-- Is the current case statement at the top level
topLevel :: Core.Expr Core.Var -> InferM Bool
topLevel e = do
  (cs, _) <- get
  return (e `notElem` cs)

-- Used to track the expression in which errors arrise
type InferME = RWST (Core.Expr Core.Var, Context) () ([Core.Expr Core.Var], Int) IO

-- Attach an expression to an erroneous computation
inExpr :: InferME a -> Core.Expr Core.Var -> InferM a
inExpr ma e = withRWST (\ctx (s, i) -> ((e, ctx), (s, i))) ma
  
-- The variables in scope and their type
newtype Context = Context {
  var :: M.Map Core.Name TypeScheme
}

-- Extract a variable from (local/global) context
safeVar :: Core.Var -> InferM TypeScheme
safeVar v = do
  ctx <- ask
  case var ctx M.!? Core.getName v of
    Just ts -> return ts
    Nothing ->
      -- We can assume the variable is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let t = Core.varType v
      in freshScheme $ toSortScheme t

-- Extract a constructor from (local/global) context
safeCon :: Core.DataCon -> (IfaceTyCon, [Core.Name], [Sort])
safeCon k = 
  let tc   = Core.dataConTyCon k
      as   = Core.getName <$> Core.dataConUnivAndExTyVars k
      args = toSort <$> Core.dataConOrigArgTys k -- Ignore evidence
  in (toIfaceTyCon tc, as, args)

-- Extract polarised and instantiated constructor arguments from context
delta :: DataCon -> [Sort] -> [Sort]
delta (DataCon (_, as, ts)) as' = subTypeVars as as' <$> ts

-- Insert a variable into the context
insertVar :: Core.Name -> TypeScheme -> Context -> Context
insertVar x f ctx = ctx{var = M.insert x f $ var ctx}

-- Insert many variable into the context
insertMany :: [Core.Name] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (f:fs) ctx = insertVar x f $ insertMany xs fs ctx





-- A fresh refinement variable
fresh :: Sort -> InferM Type
fresh (SVar a)       = return $ TVar a
fresh s@(SData _ _) = do
  (stack, i) <- get
  put (stack, i + 1)
  return $ upArrow i s
fresh (SArrow s1 s2) = do
  t1 <- fresh s1
  t2 <- fresh s2
  return (t1 :=> t2)
fresh (SApp s1 s2) = do
  t1 <- fresh s1
  return $ App t1 s2
fresh (SLit l) = return $ Lit l
fresh (SBase b as) = return $ Base b as

-- A fresh refinement scheme for module/let bindings
freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as (SVar a))       = return $ Forall as [] [] $ TVar a
freshScheme (SForall as s@(SData _ ss)) = do
  t <- fresh s
  case t of
    V x d _ -> return $ Forall as [RVar (x, d, ss)] [] t
freshScheme (SForall as (SArrow s1 s2)) = do
  Forall _ v1 _ t1 <- freshScheme (SForall [] s1)
  Forall _ v2 _ t2 <- freshScheme (SForall [] s2)
  return $ Forall as (v1 ++ v2) [] (t1 :=> t2)
freshScheme (SForall as (SApp s1 s2)) = do
  t1 <- fresh s1
  return $ Forall as [] [] $ App t1 s2
freshScheme (SForall as (SLit l)) = return $ Forall as [] [] (Lit l)
freshScheme (SForall as (SBase b ss)) = return $ Forall as [] [] (Base b ss)