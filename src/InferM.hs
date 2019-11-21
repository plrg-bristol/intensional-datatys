{-#  LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module InferM (
  InferM,
  runInferM,
  pushCase,
  popCase,
  topLevel,

  InferME,
  inExpr,
  
  Context (Context, var),
  safeVar,
  safeCon,
  upArrowDataCon,
  insertVar,
  insertMany,
  
  toSort,
  toSortScheme,
  toDataCon,
  fresh,
  freshScheme
) where

import Control.Monad.RWS

import qualified Data.Map as M

import IfaceType
import ToIface
import qualified GhcPlugins as Core
import qualified TyCoRep as T

import Types

instance Core.Uniquable IfaceTyCon where
  getUnique (IfaceTyCon n _) = Core.getUnique n

-- The inference monad;
-- a local context
-- a global expr stack for nested pattern matching, datatype reachability tree, and a fresh int
type InferM = RWST Context () ([Core.Expr Core.Var], Core.UniqFM [IfaceTyCon], Int) IO
runInferM p env = do 
  (tss, _, _) <- liftIO $ runRWST p env ([], Core.emptyUFM, 0)
  return tss

-- TODO: better comparison for top-level
instance Eq (Core.Expr Core.Var) where
  Core.Var i == Core.Var i' = Core.getUnique i == Core.getUnique i'
  _ == _ = False

-- Enter a new case statement
pushCase :: Core.Expr Core.Var-> InferM ()
pushCase c = modify (\(cs, rt, i) -> (c:cs, rt, i))

-- Exit a case statement
popCase :: InferM ()
popCase = modify (\(c:cs, rt, i) -> (cs, rt, i))

-- Is the current case statement at the top level
topLevel :: Core.Expr Core.Var -> InferM Bool
topLevel e = do
  (cs, _, _) <- get
  return (e `notElem` cs)

-- Used to track the expression in which errors arrise
type InferME = RWST (Core.Expr Core.Var, Context) () ([Core.Expr Core.Var], Core.UniqFM [IfaceTyCon], Int) IO

-- Attach an expression to an erroneous computation
inExpr :: InferME a -> Core.Expr Core.Var -> InferM a
inExpr ma e = withRWST (\ctx (s, rt, i) -> ((e, ctx), (s, rt, i))) ma
  
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

-- Extract a constructor from (local/global) context and fillout the reachability tree
safeCon :: Core.DataCon -> InferM (IfaceTyCon, [Core.Name], [Sort])
safeCon k = do
  let tc   = Core.dataConTyCon k
      as   = Core.getName <$> Core.dataConUnivAndExTyVars k
      args = toSort <$> Core.dataConOrigArgTys k -- Ignore evidence

  -- Construct reachability tree of data constructor
  (stack, rt, i) <- get
  if Core.elemUFM tc rt
    then return ()
    else do
      let rt' = Core.addToUFM rt tc [toIfaceTyCon tc' | dc <- Core.tyConDataCons tc, (T.TyConApp tc' _) <- Core.dataConOrigArgTys dc, length (Core.tyConDataCons tc') > 1]
      put (stack, rt', i)

  return (toIfaceTyCon tc, as, args)

-- Refinement a data type at a stem 
upArrow :: Int -> Sort -> Type
upArrow x (SData d as)   = V x d as
upArrow x (SArrow t1 t2) = upArrow x t1 :=> upArrow x t2
upArrow _ (SVar a)       = TVar a
upArrow x (SApp s1 s2)   = App (upArrow x s1) s2
upArrow _ (SLit l)       = Lit l
upArrow _ (SBase b as)   = Base b as

-- Instantiated constructor
upArrowDataCon :: Int -> DataCon -> [Sort] -> [Type]
upArrowDataCon x (DataCon (_, _, [])) _      = []
upArrowDataCon x (DataCon (d, as, t:ts)) as' = upArrow x (subTypeVars as as' t) : upArrowDataCon x (DataCon (d, as, ts)) as'

-- Insert a variable into the context
insertVar :: Core.Name -> TypeScheme -> Context -> Context
insertVar x f ctx = ctx{var = M.insert x f $ var ctx}

-- Insert many variable into the context
insertMany :: [Core.Name] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (f:fs) ctx = insertVar x f $ insertMany xs fs ctx





-- Extract relevant information from Core.DataCon
toDataCon :: Core.DataCon -> DataCon
toDataCon dc = DataCon (Core.getName dc, Core.getName <$> Core.dataConUnivAndExTyVars dc, toSort <$> Core.dataConOrigArgTys dc)

-- Convert a core type into a sort
toSort :: Core.Type -> Sort
toSort (T.TyVarTy v)   = SVar $ Core.getName v
toSort (T.AppTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SApp s1 s2
toSort (T.TyConApp t args) | Core.isTypeSynonymTyCon t =
  case Core.synTyConDefn_maybe t of
    Just (as, u) -> subTypeVars (Core.getName <$> as) (toSort <$> args) (toSort u)
toSort (T.TyConApp t args) = SData (toIfaceTyCon t) (toSort <$> args)
toSort (T.FunTy t1 t2) = 
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort (T.LitTy l) = SLit l
-- toSort (T.ForAllTy b t) = toSort t `applySortToSort` (SVar $ Core.getName $ Core.binderVar b)
toSort t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Cast & Coercion

-- Convert a core type into a sort scheme
toSortScheme :: Core.Type -> SortScheme
toSortScheme (T.TyVarTy v)       = SForall [] (SVar $ Core.getName v)
toSortScheme (T.AppTy t1 t2)     = SForall [] $ SApp (toSort t1) (toSort t2)
toSortScheme (T.TyConApp t args) | Core.isTypeSynonymTyCon t =
  case Core.synTyConDefn_maybe t of
    Just (as, u) -> SForall [] $ subTypeVars (Core.getName <$> as) (toSort <$> args) (toSort u)
toSortScheme (T.TyConApp t args) = SForall [] $ SData (toIfaceTyCon t) (toSort <$> args)
toSortScheme (T.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.getName $ Core.binderVar b
  in SForall (a:as) st
toSortScheme (T.FunTy t1@(T.TyConApp _ _) t2)
  | Core.isPredTy t1 = toSortScheme t2 -- Ignore evidence of typeclasses and implicit parameters
toSortScheme (T.FunTy t1 t2) = let s1 = toSort t1; SForall as s2 = toSortScheme t2 in SForall as (SArrow s1 s2)
toSortScheme t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Cast & Coercion

-- A fresh refinement variable
fresh :: Sort -> InferM Type
fresh (SVar a)       = return $ TVar a
fresh s@(SData _ _) = do
  (stack, rt, i) <- get
  put (stack, rt, i + 1)
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