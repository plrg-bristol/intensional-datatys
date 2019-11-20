{-# LANGUAGE FlexibleInstances, PatternSynonyms, MultiParamTypeClasses #-}

module Types (
  Sort (SVar, SData, SArrow, SApp, SLit, SBase),
  RVar (RVar),
  Type (Var, V, Sum, Con, Dot, TVar, (:=>), App, Lit, Base),
  DataCon (DataCon),
  SortScheme (SForall),
  TypeScheme (Forall),
  toDataCon,
  tagSumsWith,
  tvars,
  tvarsR,
  tvarsS,
  vars,
  stems,
  strip,

  refinable,
  toType,
  broaden,
  toSort,
  toSortScheme,

  -- PType,
  -- polarise,
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
  | SBase IfaceTyCon [Sort] -- Unrefinable datatypes
  | SDot

instance Eq Sort where
  SDot == t = True
  t == SDot = True
  (SVar a) == (SVar a') = a == a'
  (SData tc as) == (SData tc' as') = tc == tc' && as == as'
  (SArrow s1 s2) == (SArrow s1' s2') = s1 == s1' && s2 == s2'
  (SApp s1 s2) == (SApp s1' s2') = s1 == s1' && s2 == s2'
  (SLit l) == (SLit l') = l == l'
  (SBase tc as) == (SBase tc' as') = tc == tc' && as == as'
  _ == _ = False


-- Refinement variables
-- TODO: pattern synonym 
newtype RVar = RVar (Int, IfaceTyCon, [Sort]) deriving Eq

instance Ord RVar where
  {-# SPECIALIZE instance Ord RVar #-}
  RVar (x, _, _) <= RVar (x', _, _) = x <= x'

-- Inference types
data Type = 
    Var RVar
  | Sum Origin IfaceTyCon [Sort] [(DataCon, [Type])]
  | Dot -- Coercions

  | TVar Core.Name
  | Type :=> Type
  | App Type Sort
  | Lit T.TyLit
  | Base IfaceTyCon [Sort]

instance Eq Type where
  Dot == t = True
  t == Dot = True
  Var r == Var r' = r == r'
  Sum _ tc as cs == Sum _ tc' as' cs' = tc == tc' && as == as' && all (`elem` cs') cs && all (`elem` cs) cs'
  TVar a == TVar a' = a == a'
  (t1 :=> t2) == (t1' :=> t2') = t1 == t1' && t2 == t2'
  (Lit l) == (Lit l') = l == l'
  (Base tc as) == (Base tc' as') = tc == tc' && as == as'
  (App t s) == (App t' s') = t == t' && s == s'
  _ == _ = False

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
pattern V :: Int -> IfaceTyCon -> [Sort] -> Type
pattern V x d as = Var (RVar (x, d, as))

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

-- Type variables present in a types
tvars :: Type -> [Core.Name]
tvars (Var v)         = tvarsR v
tvars (Sum _ _ _ cs)  = [v | (_, args) <- cs, a <- args, v <- tvars a]
tvars (TVar a)        = [a]
tvars (Base _ ss)     = concatMap tvarsS ss
tvars (t1 :=> t2)     = tvars t1 ++ tvars t2
tvars (App t s)       = tvars t ++ tvarsS s
tvars _               = []

tvarsR :: RVar -> [Core.Name]
tvarsR (RVar (_, _, as)) = concatMap tvarsS as

tvarsS :: Sort -> [Core.Name]
tvarsS (SVar a) = [a]
tvarsS (SData _ as) = concatMap tvarsS as
tvarsS (SArrow s1 s2) = tvarsS s1 ++ tvarsS s2
tvarsS (SApp s1 s2) = tvarsS s1 ++ tvarsS s2
tvarsS (SBase _ as) = concatMap tvarsS as


-- The refinement variables present in a type
vars :: Type -> [RVar]
vars (Var v)         = [v]
vars (Sum _ _ _ cs)  = [v | (_, args) <- cs, a <- args, v <- vars a]
vars (t1 :=> t2)     = vars t1 ++ vars t2
vars (App t s)       = vars t
vars _               = []

-- The stems of refinement variables present in a type
stems :: Type -> [Int]
stems t = [x | RVar (x, _, _) <- vars t]

-- Strip a refinement type of type arguments
strip :: Type -> Type
strip (V x d ss)       = V x d []
strip (Sum e tc as cs) = Sum e tc [] (fmap (\(d, ts) -> (d, strip <$> ts)) cs)
strip (t1 :=> t2)      = strip t1 :=> strip t2
strip (Base tc as)     = Base tc []
strip t                = t





-- Decides whether a datatypes does not occur negatively
-- Possible optimisation, d is the only possible constructor then unrefinedable
refinable :: Core.DataCon -> Bool
refinable d = all pos (concatMap Core.dataConOrigArgTys $ Core.tyConDataCons tc)
    where
      tc :: Core.TyCon
      tc = Core.dataConTyCon d

      pos :: Core.Type -> Bool
      pos (T.FunTy t1 t2) = neg t1 && pos t2
      pos _               = True

      neg :: Core.Type -> Bool
      neg (T.TyConApp tc' _)             | tc == tc' = False
      neg (T.AppTy (T.TyConApp tc' _) _) | tc == tc' = False 
      neg (T.TyVarTy a)   = False -- Type variables may be substituted with the type itself
                                  -- Perhaps it is possible to record whether a type variable occurs +/-
      neg (T.FunTy t1 t2) = pos t1 && neg t2
      neg _               = True

-- De-refine a type to a sort
broaden :: Type -> Sort
broaden (V _ d as)      = SData d as
broaden (Sum _ tc as _) = SData tc as
broaden (TVar a)        = SVar a
broaden (t1 :=> t2)     = SArrow (broaden t1) (broaden t2)
broaden (App t1 s2)     = (broaden t1) `applySortToSort` s2
broaden (Lit l)         = SLit l
broaden (Base b as)     = SBase b as
broaden Dot             = SDot

-- Lift a sort to a type without taking fresh refinement variables
toType :: Sort -> Type
toType (SData d as)   = Base d as
toType (SBase d as)   = Base d as
toType (SVar a)       = TVar a
toType (SArrow s1 s2) = (toType s1) :=> (toType s2)
toType (SApp s1 s2)   = (toType s1) `applySort` s2
toType (SLit l)       = Lit l

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





-- -- Polarised data types (sort)
-- data PType = 
--     PVar Core.Name 
--   | PData Bool IfaceTyCon [Sort] 
--   | PArrow PType PType  
--   | PApp PType Sort
--   | PLit T.TyLit

-- -- Polarise a sort, i.e. Ty(+, -)(s) or Ty(-, +)(s)
-- polarise :: Bool -> Sort -> PType
-- polarise p (SVar a)       = PVar a
-- polarise p (SData d args) = PData p d args
-- polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)
-- polarise p (SApp s1 s2)   = PApp (polarise p s1) s2

-- Refinement a data type at a stem 
upArrow :: Int -> Sort -> Type
upArrow x (SData d as)   = V x d as
upArrow x (SArrow t1 t2) = upArrow x t1 :=> upArrow x t2
upArrow _ (SVar a)       = TVar a
upArrow x (SApp s1 s2)   = App (upArrow x s1) s2
upArrow _ (SLit l)       = Lit l
upArrow _ (SBase b as)   = Base b as





-- Substitute type variables into a type-like structure
class TypeVars a t where
  subTypeVar :: Core.Name -> t -> a -> a

-- Substitute many type variables
subTypeVars :: TypeVars a t => [Core.Name] -> [t] -> a -> a
subTypeVars _ [] = id
subTypeVars (a:as) (t:ts) = subTypeVar a t . subTypeVars as ts

-- Collapse an application type if possible after a substitution has occured
applySort :: Type -> Sort -> Type
applySort (V x d as) a           = V x d (as ++ [a])
applySort (Sum e tc as cs) a     = Sum e tc (as ++ [a]) cs
applySort (Base b as) a          = Base b (as ++ [a])
-- applySort Dot s                  = Dot
applySort t a                    = App t a -- Nonreducible

applySortToSort :: Sort -> Sort -> Sort
applySortToSort (SData d as) a = SData d (as ++ [a])
applySortToSort (SBase b as) a = SBase b (as ++ [a])
applySortToSort t a            = SApp t a

instance TypeVars Sort Sort where
  {-# SPECIALIZE instance TypeVars Sort Sort #-}
  subTypeVar a t (SVar a')
    | a == a'   = t
    | otherwise = SVar a'
  subTypeVar a t (SData d as)   = SData d (subTypeVar a t <$> as)
  subTypeVar a t (SArrow s1 s2) = SArrow (subTypeVar a t s1) (subTypeVar a t s2)
  subTypeVar a t (SApp s1 s2)   = (subTypeVar a t s1) `applySortToSort` (subTypeVar a t s2)
  subTypeVar a t (SLit l)       = SLit l
  subTypeVar a t (SBase b as)   = SBase b (subTypeVar a t <$> as)

instance TypeVars Type Type where
  {-# SPECIALIZE instance TypeVars Type Type #-}
  subTypeVar a t (V x d as)    = V x d (subTypeVar a t <$> as)
  subTypeVar a t (Sum e tc as s) = Sum e tc (subTypeVar a t <$> as) $ fmap (\(d, ts) -> (d, subTypeVar a t <$> ts)) s
  subTypeVar _ _ Dot             = Dot
  subTypeVar a t (TVar a')
    | a == a'   = t
    | otherwise = TVar a'
  subTypeVar a t (t1 :=> t2)  = subTypeVar a t t1 :=> subTypeVar a t t2
  subTypeVar a t (App t1 s2)  = subTypeVar a t t1 `applySort` subTypeVar a t s2
  subTypeVar a t (Lit l)      = Lit l
  subTypeVar a t (Base b as)  = Base b (subTypeVar a t <$> as)

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