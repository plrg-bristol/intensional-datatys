{-# LANGUAGE PatternSynonyms #-}

module Types (
  Sort (SVar, SBase, SData, SArrow, SApp),
  RVar (RVar),
  Type (Var, V, Con, TVar, Base, App, (:=>), Sum, Dot),
  SortScheme (SForall),
  TypeScheme (Forall),

  toSort,
  toSortScheme,

  PType,
  polarise,
  upArrow,

  TypeVars (subTypeVar),
  subTypeVars,
  broaden
) where

import qualified GhcPlugins as Core
import qualified TyCoRep as T

-- Base sorts (unrefined types)
data Sort = 
    SVar Core.Var 
  | SBase Core.TyCon [Sort] 
  | SData Core.TyCon [Sort] 
  | SArrow Sort Sort 
  | SApp Sort Sort 
  deriving Eq

-- Refinement variables
newtype RVar = RVar (Int, Bool, Core.TyCon, [Sort]) 
  deriving Eq

instance Ord RVar where
  RVar (x, _, _, _) <= RVar (x', _, _, _) = x <= x'

-- Inference types
data Type = 
    Var RVar
  | Sum [(Core.DataCon, [Sort], [Type])]
  | Dot -- For coercions

  | TVar Core.Var
  | Base Core.TyCon [Sort]
  | Type :=> Type
  | App Type Sort
  deriving Eq

-- Singleton sum constructor
pattern Con :: Core.DataCon -> [Sort] -> [Type] -> Type
pattern Con k as args = Sum [(k, as, args)]

-- Refinement variable pattern
pattern V :: Int -> Bool -> Core.TyCon -> [Sort] -> Type
pattern V x p d as = Var (RVar (x, p, d, as))

data SortScheme = SForall [Core.Var] Sort

-- Refinement quantified sort scheme
data TypeScheme = Forall [Core.Var] [RVar] [(Type, Type)] Type





-- Convert a core type into a sort
toSort :: Core.Type -> Sort
toSort (T.TyVarTy v)   = SVar v
toSort (T.AppTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SApp s1 s2
toSort (T.TyConApp t args) = SData t $ fmap toSort args
toSort (T.FunTy t1 t2) = 
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Forall, Literal, Cast & Coercion

-- Convert a core type into a sort scheme
toSortScheme :: Core.Type -> SortScheme
toSortScheme (T.TyVarTy v)       = SForall [] (SVar v)
toSortScheme (T.AppTy t1 t2)     = SForall [] $ SApp (toSort t1) (toSort t2)
toSortScheme (T.TyConApp t args) = SForall [] $ SData t $ fmap toSort args
toSortScheme (T.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.binderVar b
  in SForall (a:as) st
toSortScheme (T.FunTy t1@(T.TyConApp _ _) t2)
  | Core.isPredTy t1 = toSortScheme t2 -- Ignore evidence of typeclasses
toSortScheme (T.FunTy t1 t2) = let s1 = toSort t1; SForall as s2 = toSortScheme t2 in SForall as (SArrow s1 s2)





-- Polarised data types (sort)
data PType = 
    PVar Core.Var 
  | PBase Core.TyCon [Sort] 
  | PData Bool Core.TyCon [Sort] 
  | PArrow PType PType  
  | PApp PType Sort

-- Polarise a sort, i.e. Ty(+, -)(s) or Ty(-, +)(s)
polarise :: Bool -> Sort -> PType
polarise p (SVar a)       = PVar a
polarise p (SBase b as)   = PBase b as
polarise p (SData d args) = PData p d args
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)
polarise p (SApp s1 s2)   = PApp (polarise p s1) s2

-- Refinement a polarised data type at a stem 
upArrow :: Int -> PType -> Type
upArrow x (PData p d as) = V x p d as
upArrow x (PArrow t1 t2) = upArrow x t1 :=> upArrow x t2
upArrow x (PVar a)       = TVar a
upArrow x (PBase b as)   = Base b as
upArrow x (PApp s1 s2)   = App (upArrow x s1) s2





-- Substitute type variables into a type-like structure
class TypeVars a where
  subTypeVar :: Core.Var -> a -> a -> a

-- Substitute many variables
subTypeVars :: TypeVars a => [Core.Var] -> [a] -> a -> a
subTypeVars [] [] = id
subTypeVars (a:as) (t:ts) = subTypeVar a t . subTypeVars as ts

instance TypeVars Sort where
  subTypeVar a t (SVar a')
    | a == a'   = t
    | otherwise = SVar a'
  subTypeVar a t (SBase b as)   = SBase b (subTypeVar a t <$> as)
  subTypeVar a t (SData d as)   = SData d (subTypeVar a t <$> as)
  subTypeVar a t (SArrow s1 s2) = SArrow (subTypeVar a t s1) (subTypeVar a t s2)
  subTypeVar a t (SApp s1 s2)   = SApp (subTypeVar a t s1) (subTypeVar a t s2)

instance TypeVars Type where
  subTypeVar a t (V x p d as) = V x p d (subTypeVar a (broaden t) <$> as)
  subTypeVar a t (Sum s)      = Sum $ fmap (\(d, as, ts) -> (d, subTypeVar a (broaden t) <$> as, subTypeVar a t <$> ts)) s
  subTypeVar _ _ Dot          = Dot
  subTypeVar a t (TVar a')
    | a == a'   = t
    | otherwise = TVar a'
  subTypeVar a t (Base b as)  = Base b (subTypeVar a (broaden t) <$> as)
  subTypeVar a t (t1 :=> t2)  = subTypeVar a t t1 :=> subTypeVar a t t2
  subTypeVar a t (App t1 s2)  = subTypeVar a t t1 `applySort` subTypeVar a (broaden t) s2

-- Derefine a type to a sort
broaden :: Type -> Sort
broaden (V _ _ d as)          = SData d as
broaden (Sum ((d, as, ts):_)) = SData (Core.dataConTyCon d) as -- Sum must be homogeneous
broaden (TVar a)              = SVar a
broaden (Base b as)           = SBase b as
broaden (t1 :=> t2)           = SArrow (broaden t1) (broaden t2)
broaden (App t1 s2)           = SApp (broaden t1) s2

-- Collapse an application type if possible after a substitution has occured
applySort :: Type -> Sort -> Type
applySort (V x p d as) a    = V x p d (as ++ [a])
applySort (Base b as) a     = Base b (as ++ [a])
applySort (Con k as args) a = Con k (as ++ [a]) args
applySort t a               = App t a