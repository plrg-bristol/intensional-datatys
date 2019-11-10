{-# LANGUAGE DefaultSignatures, DeriveGeneric, PatternSynonyms, MultiParamTypeClasses #-}

module Types (
  Sort (SVar, SBase, SData, SArrow, SApp),
  RVar (RVar),
  Type (Var, V, Sum, Con, Dot, TVar, Base, (:=>), App),
  SortScheme (SForall),
  TypeScheme (Forall),
  vars,
  stems,

  toSort,
  toSortScheme,

  PType,
  polarise,
  upArrow,

  TypeVars (subTypeVar),
  subTypeVars,
  subRefinementVar,
  subRefinementVars,
  subRefinementMap
) where

import GHC.Generics

-- import Data.Serialize
import qualified Data.Map as M

import qualified GhcPlugins as Core
import qualified TyCoRep as T

-- Base sorts (unrefined types)
data Sort = 
    SVar Core.Var 
  | SBase Core.TyCon [Sort] 
  | SData Core.TyCon [Sort] 
  | SArrow Sort Sort 
  | SApp Sort Sort 
  deriving (Eq, Generic)
-- instance Serialize Sort

-- Refinement variables
newtype RVar = RVar (Int, Bool, Core.TyCon, [Sort]) deriving (Eq, Generic)
-- instance Serialize RVar

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
  deriving (Eq, Generic)
-- instance Serialize Type

-- Singleton sum constructor
pattern Con :: Core.DataCon -> [Sort] -> [Type] -> Type
pattern Con k as args = Sum [(k, as, args)]

-- Refinement variable pattern
pattern V :: Int -> Bool -> Core.TyCon -> [Sort] -> Type
pattern V x p d as = Var (RVar (x, p, d, as))

data SortScheme = SForall [Core.Var] Sort

-- Refinement quantified sort scheme
data TypeScheme = Forall [Core.Var] [RVar] [(Type, Type)] Type deriving Generic
-- instance Serialize TypeScheme

-- The refinement variables present in a type
vars :: Type -> [RVar]
vars (Var v)     = [v]
vars (Sum cs)    = [v | (_, _, args) <- cs, a <- args, v <- vars a]
vars (t1 :=> t2) = vars t1 ++ vars t2
vars (App t s)   = vars t
vars _           = []

-- The stems of refinement variables present in a type
stems :: Type -> [Int]
stems t = [x | RVar (x, _, _, _) <- vars t]





-- Convert a core type into a sort
toSort :: Core.Type -> Sort
toSort (T.TyVarTy v)   = SVar v
toSort (T.AppTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SApp s1 s2
toSort (T.TyConApp t args) = SData t (toSort <$> args)
toSort (T.FunTy t1 t2) = 
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Forall, Literal, Cast & Coercion

-- Convert a core type into a sort scheme
toSortScheme :: Core.Type -> SortScheme
toSortScheme (T.TyVarTy v)       = SForall [] (SVar v)
toSortScheme (T.AppTy t1 t2)     = SForall [] $ SApp (toSort t1) (toSort t2)
toSortScheme (T.TyConApp t args) = SForall [] $ SData t (toSort <$> args)
toSortScheme (T.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.binderVar b
  in SForall (a:as) st
toSortScheme (T.FunTy t1@(T.TyConApp _ _) t2)
  | Core.isPredTy t1 = toSortScheme t2 -- Ignore evidence of typeclasses and implicit parameters
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
class TypeVars a t where
  subTypeVar :: Core.Var -> t -> a -> a

-- Substitute many type variables
subTypeVars :: TypeVars a t => [Core.Var] -> [t] -> a -> a
subTypeVars [] [] = id
subTypeVars (a:as) (t:ts) = subTypeVar a t . subTypeVars as ts

-- De-refine a type to a sort
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
applySort t a               = App t a -- Nonreducible

instance TypeVars Sort Sort where
  {-# SPECIALIZE instance TypeVars Sort Sort #-}
  subTypeVar a t (SVar a')
    | a == a'   = t
    | otherwise = SVar a'
  subTypeVar a t (SBase b as)   = SBase b (subTypeVar a t <$> as)
  subTypeVar a t (SData d as)   = SData d (subTypeVar a t <$> as)
  subTypeVar a t (SArrow s1 s2) = SArrow (subTypeVar a t s1) (subTypeVar a t s2)
  subTypeVar a t (SApp s1 s2)   = SApp (subTypeVar a t s1) (subTypeVar a t s2)

instance TypeVars Type Type where
  {-# SPECIALIZE instance TypeVars Type Type #-}
  subTypeVar a t (V x p d as) = V x p d (subTypeVar a t <$> as)
  subTypeVar a t (Sum s)      = Sum $ fmap (\(d, as, ts) -> (d, subTypeVar a t <$> as, subTypeVar a t <$> ts)) s
  subTypeVar _ _ Dot          = Dot
  subTypeVar a t (TVar a')
    | a == a'   = t
    | otherwise = TVar a'
  subTypeVar a t (Base b as)  = Base b (subTypeVar a t <$> as)
  subTypeVar a t (t1 :=> t2)  = subTypeVar a t t1 :=> subTypeVar a t t2
  subTypeVar a t (App t1 s2)  = subTypeVar a t t1 `applySort` subTypeVar a t s2

instance TypeVars Sort Type where
  {-# SPECIALIZE instance TypeVars Sort Type #-}
  subTypeVar a t = subTypeVar a (broaden t)

-- Substitute refinement variables into a type
subRefinementVar :: RVar -> Type -> Type -> Type
subRefinementVar x y (Var x')
  | x == x' = y
subRefinementVar x y (Sum s)     = Sum $ fmap (\(d, as, ts) -> (d, as, subRefinementVar x y <$> ts)) s
subRefinementVar x y (t1 :=> t2) = (subRefinementVar x y t1) :=> (subRefinementVar x y t2)
subRefinementVar x y (App t1 s2) = App (subRefinementVar x y t1) s2 -- If refinement variables can induce type level reduction we lose orthogonality (and maybe soundness?)
subRefinementVar _ _ t = t

-- Substitute many refinement variables
subRefinementVars :: [RVar] -> [Type] -> Type -> Type
subRefinementVars [] [] = id
subRefinementVars (a:as) (t:ts) = subRefinementVar a t . subRefinementVars as ts

-- Substitute refinement variables from a map
subRefinementMap :: M.Map RVar Type -> Type -> Type
subRefinementMap m = subRefinementVars as ts
  where
    as = M.keys m
    ts = M.elems m