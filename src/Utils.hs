module Utils
    (
      toSortScheme,
      toSort,
      isConstructor,
      fromPolyVar,
      isWild,
      name
    ) where

import Types
import Data.List
import qualified TyCoRep as T
import qualified GhcPlugins as Core

toSort :: Core.Type -> Sort
toSort (T.TyVarTy v) = SVar v
toSort (T.FunTy t1 t2) = SArrow (toSort t1) (toSort t2)
toSort (T.LitTy _) = error "Unimplemented"
toSort _ = error "Core type is not a valid sort."

toSortScheme :: Core.Type -> SortScheme
toSortScheme (T.TyVarTy v) = SForall [] (SVar v)
toSortScheme (T.FunTy t1 t2) =
  let SForall [] s1 = toSortScheme t1
      SForall [] s2 = toSortScheme t2
  in SForall [] (SArrow s1 s2)
toSortScheme (T.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.binderVar b
  in SForall (a:as) st
toSortScheme (T.TyConApp c args) = SForall [] $ SData c
toSortScheme _ = error "Unimplemented"

isConstructor :: Core.Var -> Bool
isConstructor x = case Core.varType x of
  T.TyConApp _ _ -> True
  otherwise -> False

isWild :: Core.Var -> Bool
isWild x = name x == "$_sys$wild"

name :: Core.NamedThing a => a -> String
name = Core.nameStableString . Core.getName

fromPolyVar :: Core.CoreExpr -> Maybe (Core.Id, [Sort])
fromPolyVar (Core.Var i) = Just (i, [])
fromPolyVar (Core.App e1 (Core.Type t)) = do
  (id, ts) <- fromPolyVar e1
  return (id, toSort t:ts)
fromPolyVar _ = Nothing
