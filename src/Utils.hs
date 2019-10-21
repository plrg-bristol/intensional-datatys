module Utils
    (
      Var,
      toSortScheme,
      toSort,
      isConstructor,
      fromPolyVar,
      isWild
    ) where

import Types
import Data.List
import qualified TyCoRep as T
import qualified GhcPlugins as Core

-- Exposed for Inferm
type Var = Core.Var

toSort :: Core.Type -> Sort
toSort (T.TyVarTy v) = SVar v
toSort (T.FunTy t1 t2) = SArrow (toSort t1) (toSort t2)
toSort _ = error "Core type is not a valid sort."

toSortScheme :: Core.Type -> SortScheme
toSortScheme (T.TyVarTy v) = SForall [] (SVar v)
toSortScheme (T.FunTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SForall [] (SArrow s1 s2)
toSortScheme (T.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.binderVar b
  in SForall (a:as) st
toSortScheme _ = error "Core type is not a valid sort scheme."

isConstructor :: Var -> Bool
isConstructor x = isPrefixOf "" (Core.nameStableString $ Core.getName x)

isWild :: Var -> Bool
isWild x = (Core.nameStableString $ Core.getName x) == "$_sys$wild"

fromPolyVar :: Core.CoreExpr -> Maybe (Core.Id, [Sort])
fromPolyVar (Core.Var i) = Just (i, [])
fromPolyVar (Core.App e1 (Core.Type t)) = do
  (id, ts) <- fromPolyVar e1
  return (id, toSort t:ts)
fromPolyVar _ = Nothing
