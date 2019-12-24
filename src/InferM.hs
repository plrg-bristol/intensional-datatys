{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module InferM (
 
) where

import Control.Monad.RWS

import qualified Data.Map as M

import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr

import Types
import Constraint

-- The variables in scope and their type
type Context = M.Map Core.Name (ConSet, Type P T) 

-- The inference monad;
-- a local context
-- a global expr stack for nested pattern matching, a fresh int
type InferM m = RWST Context () ([Core.Unique], Int) m
runInferM p env = do 
  (tss, _, _) <- liftIO $ runRWST p env ([], 0)
  return tss

instance Monad m => Fresh (InferM m) where
  type E (InferM m) = T
  inj t = do
    (stack, i) <- get
    put (stack, i + 1)
    return (Inj i t)

-- Enter a new case statement
pushCase :: Monad m => Core.Expr Core.Var -> InferM m ()
pushCase (Core.Var v) = modify (\(us, i) -> (Core.getUnique v:us, i))
 
-- Exit a case statement
popCase :: Monad m => InferM m ()
popCase = modify (\(u:us, i) -> (us, i))
 
-- Is the current case statement at the top level
topLevel :: Monad m => Core.Expr Core.Var -> InferM m Bool
topLevel (Core.Var v) = do
  (us, _) <- get
  return (Core.getUnique v `notElem` us)
topLevel _ = error "Cannot pattern match on a non variable!"
 
-- Extract a constructor from (local/global) context
safeCon :: Monad m => Core.DataCon -> [Core.Type] -> InferM m (Core.Name, [Type P T]) 
safeCon k ts = do 
  let tc   = Core.dataConTyCon k
      as   = Core.dataConUnivAndExTyVars k
      args = Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as ts)) <$> Core.dataConOrigArgTys k -- Ignore evidence
  args' <- mapM fromCore args
  return (Core.getName tc, args')
 
-- Extract a variable from (local/global) context
safeVar :: Monad m => Core.Var -> [Core.Type] -> InferM m (ConSet, Type P T) 
safeVar v ts = do
  ctx <- ask
  case ctx M.!? Core.getName v of
    Just (cs, t) -> do
      ts' <- mapM fromCore ts
      return (cs, applyTyVars t ts')
    Nothing -> do
      -- We can assume the variable is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let (as, t) = dequantify $ Core.varType v
      let t' = Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as ts)) t
      t'' <- fromCore t'
      return (M.empty, t'')

dequantify :: Core.Type -> ([Core.TyVar], Core.Type)
dequantify (Tcr.ForAllTy b t) =
  let (as, st) = dequantify t
      a = Core.binderVar b
  in (a:as, st)
dequantify (Tcr.FunTy t1@(Tcr.TyConApp _ _) t2)
  | Core.isPredTy t1 = dequantify t2 -- Ignore evidence of typeclasses and implicit parameters
dequantify t = ([], t)
