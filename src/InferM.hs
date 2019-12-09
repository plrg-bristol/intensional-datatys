{-# LANGUAGE BangPatterns #-}

module InferM (
  Context,
  insertVar,
  insertMany,

  InferM,
  runInferM,
  freshVar,
  pushCase,
  popCase,
  topLevel,
  safeCon,
  safeVar,
  refinable,

  upArrow,
  fresh,
  freshScheme,

  quantifyWith
) where

import Data.Bifunctor
import Constraint
import Control.Monad.RWS
import qualified Data.Map as M
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core
import IfaceType
import ToIface
import Debug.Trace
import CoreSubst

-- The variables in scope and their type
type Context = M.Map Core.Name TypeScheme

-- Insert a variable into the context
insertVar :: Core.Name -> TypeScheme -> Context -> Context
insertVar = M.insert

-- Insert many variable into the context
insertMany :: [Core.Name] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (f:fs) ctx = insertVar x f $ insertMany xs fs ctx






-- The inference monad;
-- a local context
-- a global expr stack for nested pattern matching, a fresh int, and IO for timings
type InferM = RWST Context () ([Core.Unique], Int) IO
runInferM p env = do 
  (tss, _, _) <- liftIO $ runRWST p env ([], 0)
  return tss

freshVar :: InferM Int
freshVar = do
  (stack, i) <- get 
  put (stack, i + 1)
  return i

-- Enter a new case statement
pushCase :: Core.Expr Core.Var-> InferM ()
pushCase (Core.Var v) = modify $ first ((:) $ Core.getUnique v)

-- Exit a case statement
popCase :: InferM ()
popCase = modify (\(u:us, i) -> (us, i))

-- Is the current case statement at the top level
topLevel :: Core.Expr Core.Var -> InferM Bool
topLevel (Core.Var v) = do
  (us, _) <- get
  return (Core.getUnique v `notElem` us)
topLevel _ = error "Cannot pattern match on a non variable!"

-- Extract a constructor from (local/global) context
safeCon :: Core.DataCon -> [Core.Type] -> InferM (Core.Name, [Type])
-- safeCon x ts | Core.pprTrace "safeCon" (Core.ppr x) False = undefined 
safeCon k ts = do 
  let tc   = Core.dataConTyCon k
      as   = Core.dataConUnivAndExTyVars k
      args = substTy (extendTvSubstList emptySubst (zip as ts)) <$> Core.dataConOrigArgTys k -- Ignore evidence
  args' <- mapM fresh args
  return (Core.getName tc, args')

-- Extract a variable from (local/global) context
safeVar :: Core.Var -> [Core.Type] -> InferM (ConGraph, Type)
-- safeVar x ts | Core.pprTrace "safeVar" (Core.ppr x) False = undefined 
safeVar v ts = do
  ctx <- ask
  -- !() <- Core.pprTraceM "v" (Core.ppr v)
  case ctx M.!? Core.getName v of
    Just (Forall as cg u) -> do
      ts' <- mapM fresh ts
      return (cg, subTyVars as ts' u)
    Nothing -> do
      -- We can assume the variable is in scope as GHC hasn't emitted a warning
      -- Assume all externally defined terms are unrefined
      let (as, t) = dequantify $ Core.varType v
      let t' = substTy (extendTvSubstList emptySubst (zip as ts)) t
      t'' <- fresh t'
      return (empty, t'')

dequantify :: Core.Type -> ([Core.TyVar], Core.Type)
dequantify (Tcr.ForAllTy b t) =
  let (as, st) = dequantify t
      a = Core.binderVar b
  in (a:as, st)
dequantify (Tcr.FunTy t1@(Tcr.TyConApp _ _) t2)
  | Core.isPredTy t1 = dequantify t2 -- Ignore evidence of typeclasses and implicit parameters
dequantify t = ([], t)

subTyVars :: [Core.Name] -> [Type] -> Type -> Type
subTyVars (a:as) (t:ts) (TVar a')
  | a == a' = t
  | otherwise = subTyVars as ts (TVar a')
subTyVars as ts (t1 :=> t2) = subTyVars as ts t1 :=> subTyVars as ts t2
subTyVars as ts t = t

-- Decides whether a datatypes only occurs positively
refinable :: Core.DataCon -> Bool
refinable d = (length (Core.tyConDataCons tc) > 1) && all pos (concatMap Core.dataConOrigArgTys $ Core.tyConDataCons tc)
    where
      tc :: Core.TyCon
      tc = Core.dataConTyCon d

      pos :: Core.Type -> Bool
      pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
      pos _                 = True

      neg :: Core.Type -> Bool
      neg (Tcr.TyConApp tc' _)               | tc == tc' = False
      neg (Tcr.AppTy (Tcr.TyConApp tc' _) _) | tc == tc' = False 
      neg (Tcr.TyVarTy a)   = False -- Type variables may be substituted with the type itself
                                    -- Perhaps it is possible to record whether a type variable occurs +/-
      neg (Tcr.FunTy t1 t2) = pos t1 && neg t2
      neg _                 = True





upArrow :: Int -> Type -> Type
upArrow i (t1 :=> t2) = upArrow i t1 :=> upArrow i t2
upArrow i (Inj _ d) = Inj i d
upArrow _ t = t

-- A fresh refinement variable
fresh :: Core.Type -> InferM Type
fresh = fresh' . toSort

fresh' :: Sort -> InferM Type
fresh' (SBase b)   = return $ Base b
fresh' (SVar a)    = return $ TVar a
fresh' (SArrow s1 s2) = do
  t1 <- fresh' s1
  t2 <- fresh' s2
  return (t1 :=> t2)
fresh' (SData d) = do
  i <- freshVar
  return $ Inj i d
fresh' (SApp s1 s2) = return $ App s1 s2
fresh' (SLit l)     = return $ Lit l

-- Convert a core type into a sort
toSort :: Core.Type -> Sort
toSort (Tcr.TyVarTy v)   = SVar $ Core.getName v
toSort (Tcr.AppTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SApp s1 s2
toSort (Tcr.TyConApp t args) 
  | Core.isTypeSynonymTyCon t
  , Just (as, u) <- Core.synTyConDefn_maybe t
  = toSort $ substTy (extendTvSubstList emptySubst (zip as args)) u
  
  | otherwise 
  = SData (Core.getName t)
toSort (Tcr.FunTy t1 t2) = 
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort (Tcr.LitTy l) = SLit l
toSort t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Forall, Cast, and Coercion

-- A fresh refinement scheme for module/let bindings
freshScheme :: Core.Type -> InferM TypeScheme
freshScheme = freshScheme' . toSortScheme

freshScheme' :: SortScheme -> InferM TypeScheme
freshScheme' (SForall as (SVar a))       = return $ Forall as empty $ TVar a
freshScheme' (SForall as s@(SData _)) = do
  t <- fresh' s
  case t of
    Inj x d -> return $ Forall as (declare x d empty) t
freshScheme' (SForall as (SArrow s1 s2)) = do
  Forall _ cg1 t1 <- freshScheme' (SForall [] s1)
  Forall _ cg2 t2 <- freshScheme' (SForall [] s2)
  return $ Forall as (cg1 `union` cg2) (t1 :=> t2)
freshScheme' (SForall as (SApp s1 s2)) = return $ Forall as empty $ App s1 s2
freshScheme' (SForall as (SLit l)) = return $ Forall as empty (Lit l)
freshScheme' (SForall as (SBase b)) = return $ Forall as empty (Base b)

-- Convert a core type into a sort scheme
toSortScheme :: Core.Type -> SortScheme
toSortScheme (Tcr.TyVarTy v)   = SForall [] $ SVar $ Core.getName v
toSortScheme (Tcr.AppTy t1 t2) = SForall [] $ SApp (toSort t1) (toSort t2)
toSortScheme (Tcr.TyConApp t args) 
  | Core.isTypeSynonymTyCon t
  , Just (as, u) <- Core.synTyConDefn_maybe t
  = toSortScheme $ substTy (extendTvSubstList emptySubst (zip as args)) u
  
  | otherwise 
  = SForall [] $ SData (Core.getName t)
toSortScheme (Tcr.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.getName $ Core.binderVar b
  in SForall (a:as) st
toSortScheme (Tcr.FunTy t1@(Tcr.TyConApp _ _) t2)
  | Core.isPredTy t1 = toSortScheme t2 -- Ignore evidence of typeclasses and implicit parameters
toSortScheme (Tcr.FunTy t1 t2) = 
  let s1 = toSort t1
      SForall as s2 = toSortScheme t2
  in SForall as (SArrow s1 s2)
toSortScheme t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Cast & Coercion

quantifyWith :: ConGraph -> [TypeScheme] -> InferM [TypeScheme]
quantifyWith cg ts = do
  -- Stems which occur in the interface
  let interfaceStems = [s | (Forall _ _ u) <- ts, s <- stems u]

  let cg' = restrict interfaceStems $ transitive cg

  return [Forall as cg' u | Forall as _ u <- ts]