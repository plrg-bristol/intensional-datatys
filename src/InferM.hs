module InferM (
  Context,
  insertVar,
  insertMany,

  InferM,
  pushCase,
  popCase,
  topLevel,

  fresh
) where

import Constraint
import Control.Monad.RWS
import qualified Data.Map as M
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core
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

-- Enter a new case statement
pushCase :: Core.Expr Core.Var-> InferM ()
pushCase (Core.Var v) = modify (\(us, i) -> (Core.getUnique v:us, i))

-- Exit a case statement
popCase :: InferM ()
popCase = modify (\(u:us, i) -> (us, i))

-- Is the current case statement at the top level
topLevel :: Core.Expr Core.Var -> InferM Bool
topLevel (Core.Var v) = do
  (us, _) <- get
  return (Core.getUnique v `notElem` us)
topLevel _ = error "Cannot pattern match on a non variable!"






-- A fresh refinement variable
fresh :: Core.Type -> InferM Type
fresh = fresh' . toSort
  where
    fresh' :: Sort -> InferM Type
    fresh' (SBase b as)   = return $ Base b as
    fresh' (SVar a)       = return $ TVar a
    fresh' (SArrow s1 s2) = do
      t1 <- fresh' s1
      t2 <- fresh' s2
      return (t1 :=> t2)
    fresh' (SData d as) = do
      (stack, i) <- get
      put (stack, i + 1)
      return $ Inj i d as
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
  = SData (Core.getName t) (fmap toSort args)
toSort (Tcr.FunTy t1 t2) = 
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort (Tcr.LitTy l) = SLit l
toSort t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Forall, Cast, and Coercion