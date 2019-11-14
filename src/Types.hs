{-# LANGUAGE FlexibleInstances, PatternSynonyms, MultiParamTypeClasses #-}

module Types (
  Sort (SVar, SData, SArrow, SApp, SLit),
  RVar (RVar),
  Type (Var, V, Sum, Con, Dot, TVar, (:=>), App, Lit),
  DataCon (DataCon),
  SortScheme (SForall),
  TypeScheme (Forall),
  toDataCon,
  tagSumsWith,
  vars,
  stems,

  broaden,
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

import qualified Data.Map as M

import IfaceType
import ToIface
import qualified GhcPlugins as Core
import qualified TyCoRep as T

-- For tracking the origin of sums, used in error messages
type Origin = Either (Core.Expr Core.Var) Core.ModuleName

-- Base sorts (unrefined types)
data Sort = 
    SVar Core.Name 
  | SData IfaceTyCon [Sort] 
  | SArrow Sort Sort 
  | SApp Sort Sort 
  | SLit T.TyLit
  deriving Eq

-- Refinement variables
-- TODO: pattern synonym 
newtype RVar = RVar (Int, Bool, IfaceTyCon, [Sort]) deriving Eq

instance Ord RVar where
  {-# SPECIALIZE instance Ord RVar #-}
  RVar (x, _, _, _) <= RVar (x', _, _, _) = x <= x'

-- Inference types
data Type = 
    Var RVar
  | Sum Origin IfaceTyCon [Sort] [(DataCon, [Type])]
  | Dot -- Coercions

  | TVar Core.Name
  | Type :=> Type
  | App Type Sort
  | Lit T.TyLit
  deriving Eq

-- Equality of sums does not depend on their expression of origin
instance Eq (Core.Expr Core.Var) where
  {-# SPECIALIZE instance Eq (Core.Expr Core.Var) #-}
  e1 == e2 = True

-- Lightweight representation of Core.DataCon:
-- DataCon n as args ~~ n :: forall as . args_0 -> ... -> args_n
-- TODO: pattern synonym
newtype DataCon = DataCon (Core.Name, [Core.Name], [Sort])

-- DataCons are uniquely determined by their constructor's name
instance Eq DataCon where
  {-# SPECIALIZE instance Eq DataCon #-}
  DataCon (n, _, _) == DataCon (n', _, _) = n == n'

-- Extract relevant information from Core.DataCon
toDataCon :: Core.DataCon -> DataCon
toDataCon dc = DataCon (Core.getName dc, Core.getName <$> Core.dataConUnivAndExTyVars dc, toSort <$> Core.dataConOrigArgTys dc)

-- Singleton sum constructor
pattern Con :: Origin -> IfaceTyCon -> DataCon -> [Sort] -> [Type] -> Type
pattern Con e tc k as args = Sum e tc as [(k, args)]

-- Refinement variable pattern
pattern V :: Int -> Bool -> IfaceTyCon -> [Sort] -> Type
pattern V x p d as = Var (RVar (x, p, d, as))

data SortScheme = SForall [Core.Name] Sort

-- Refinement quantified sort scheme
data TypeScheme = Forall [Core.Name] [RVar] [(Type, Type)] Type
-- instance Serialize TypeScheme

-- Associate Sum types with their module of origin
tagSumsWith :: Core.ModuleName -> TypeScheme -> TypeScheme
tagSumsWith m (Forall xs rs cs u) = Forall xs rs ((\(t1, t2) -> (tagSumsWith' t1, tagSumsWith' t2)) <$> cs) (tagSumsWith' u)
  where
    tagSumsWith' :: Type -> Type
    tagSumsWith' (Sum _ tc ss cs) = Sum (Right m) tc ss [(d, tagSumsWith' <$> ts) | (d, ts) <- cs]
    tagSumsWith' t = t

-- The refinement variables present in a type
vars :: Type -> [RVar]
vars (Var v)         = [v]
vars (Sum _ _ _ cs)  = [v | (_, args) <- cs, a <- args, v <- vars a]
vars (t1 :=> t2)     = vars t1 ++ vars t2
vars (App t s)       = vars t
vars _               = []

-- The stems of refinement variables present in a type
stems :: Type -> [Int]
stems t = [x | RVar (x, _, _, _) <- vars t]





-- De-refine a type to a sort
broaden :: Type -> Sort
broaden (V _ _ d as)    = SData d as
broaden (Sum _ tc as _) = SData tc as
broaden (TVar a)        = SVar a
broaden (t1 :=> t2)     = SArrow (broaden t1) (broaden t2)
broaden (App t1 s2)     = SApp (broaden t1) s2

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
toSort t = Core.pprPanic "Core type is not a valid sort!" (Core.ppr t) -- Forall, Cast & Coercion

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





-- Polarised data types (sort)
data PType = 
    PVar Core.Name 
  | PData Bool IfaceTyCon [Sort] 
  | PArrow PType PType  
  | PApp PType Sort
  | PLit T.TyLit

-- Polarise a sort, i.e. Ty(+, -)(s) or Ty(-, +)(s)
polarise :: Bool -> Sort -> PType
polarise p (SVar a)       = PVar a
polarise p (SData d args) = PData p d args
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)
polarise p (SApp s1 s2)   = PApp (polarise p s1) s2

-- Refinement a polarised data type at a stem 
upArrow :: Int -> PType -> Type
upArrow x (PData p d as) = V x p d as
upArrow x (PArrow t1 t2) = upArrow x t1 :=> upArrow x t2
upArrow x (PVar a)       = TVar a
upArrow x (PApp s1 s2)   = App (upArrow x s1) s2





-- Substitute type variables into a type-like structure
class TypeVars a t where
  subTypeVar :: Core.Name -> t -> a -> a

-- Substitute many type variables
subTypeVars :: TypeVars a t => [Core.Name] -> [t] -> a -> a
subTypeVars [] [] = id
subTypeVars (a:as) (t:ts) = subTypeVar a t . subTypeVars as ts

-- Collapse an application type if possible after a substitution has occured
applySort :: Type -> Sort -> Type
applySort (V x p d as) a         = V x p d (as ++ [a])
applySort (Con e tc d as args) a = Con e tc d (as ++ [a]) args
applySort t a                    = App t a -- Nonreducible

instance TypeVars Sort Sort where
  {-# SPECIALIZE instance TypeVars Sort Sort #-}
  subTypeVar a t (SVar a')
    | a == a'   = t
    | otherwise = SVar a'
  subTypeVar a t (SData d as)   = SData d (subTypeVar a t <$> as)
  subTypeVar a t (SArrow s1 s2) = SArrow (subTypeVar a t s1) (subTypeVar a t s2)
  subTypeVar a t (SApp s1 s2)   = SApp (subTypeVar a t s1) (subTypeVar a t s2)

instance TypeVars Type Type where
  {-# SPECIALIZE instance TypeVars Type Type #-}
  subTypeVar a t (V x p d as)    = V x p d (subTypeVar a t <$> as)
  subTypeVar a t (Sum e tc as s) = Sum e tc (subTypeVar a t <$> as) $ fmap (\(d, ts) -> (d, subTypeVar a t <$> ts)) s
  subTypeVar _ _ Dot             = Dot
  subTypeVar a t (TVar a')
    | a == a'   = t
    | otherwise = TVar a'
  subTypeVar a t (t1 :=> t2)  = subTypeVar a t t1 :=> subTypeVar a t t2
  subTypeVar a t (App t1 s2)  = subTypeVar a t t1 `applySort` subTypeVar a t s2

instance TypeVars Sort Type where
  {-# SPECIALIZE instance TypeVars Sort Type #-}
  subTypeVar a t = subTypeVar a (broaden t)

-- Substitute refinement variables into a type
subRefinementVar :: RVar -> Type -> Type -> Type
subRefinementVar x y (Var x')
  | x == x' = y
subRefinementVar x y (Sum e tc as s) = Sum e tc as $ fmap (\(d, ts) -> (d, subRefinementVar x y <$> ts)) s
subRefinementVar x y (t1 :=> t2)     = (subRefinementVar x y t1) :=> (subRefinementVar x y t2)
subRefinementVar x y (App t1 s2)     = App (subRefinementVar x y t1) s2 -- If refinement variables can induce type level reduction we lose orthogonality (and maybe soundness?)
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