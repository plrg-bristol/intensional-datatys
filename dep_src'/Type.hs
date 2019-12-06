{-# LANGUAGE PatternSynonyms, MultiParamTypeClasses, FlexibleInstances #-}

module Type (
  Type (.., Con),
  injs,
  toType,
  Sort(..),
  SortScheme(..),
  refinable,

  subTypeVars
) where

import IfaceType
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core

-- Base sorts (unrefined types)
data Sort = 
    SVar Core.Name 
  | SData Core.Name [Sort] 
  | SArrow Sort Sort 
  | SApp Sort Sort 
  | SLit Tcr.TyLit
  | SBase Core.Name [Sort] -- Unrefinable datatypes
  deriving Eq

data SortScheme = SForall [Core.Name] Sort

data Type = 
    Base Core.Name      [Sort]
  | TVar Core.Name
  | Type :=> Type 
  | Inj Int Core.Name   [Sort]
  | Sum [Core.Name]     [Sort]

  | App Type Sort
  | Lit Tcr.TyLit
  | Dot
  deriving Eq

pattern Con :: Core.Name -> [Sort] -> Type
pattern Con k as = Sum [k] as

-- Lift a sort to a type without taking fresh refinement variables
toType :: Sort -> Type
toType (SData d as)   = Base d as
toType (SBase d as)   = Base d as
toType (SVar a)       = TVar a
toType (SArrow s1 s2) = (toType s1) :=> (toType s2)
toType (SApp s1 s2)   = (toType s1) `applySort` s2
toType (SLit l)       = Lit l

-- Subrefinement variables which appear in the type
injs :: Type -> [(Int, Core.Name)]
injs (t1 :=> t2)  = injs t1 ++ injs t2
injs (Inj i d as) = [(i, d)]
injs _            = []

-- Decides whether a datatypes only occurs positively
refinable :: Core.DataCon -> Bool
refinable d = (length (Core.tyConDataCons tc) > 1) && all pos (concatMap Core.dataConOrigArgTys $ Core.tyConDataCons tc)
    where
      tc :: Core.TyCon
      tc = Core.dataConTyCon d

      pos :: Core.Type -> Bool
      pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
      pos _               = True

      neg :: Core.Type -> Bool
      neg (Tcr.TyConApp tc' _)             | tc == tc' = False
      neg (Tcr.AppTy (Tcr.TyConApp tc' _) _) | tc == tc' = False 
      neg (Tcr.TyVarTy a)   = False -- Type variables may be substituted with the type itself
                                    -- Perhaps it is possible to record whether a type variable occurs +/-
      neg (Tcr.FunTy t1 t2) = pos t1 && neg t2
      neg _               = True

-- Substitute type variables into a type-like structure
class TypeVars a t where
  subTypeVar :: Core.Name -> t -> a -> a

instance (Functor f, TypeVars a t) => TypeVars (f a) t where
  subTypeVar as ts = fmap $ subTypeVar as ts

-- Substitute many type variables
subTypeVars :: TypeVars a t => [Core.Name] -> [t] -> a -> a
subTypeVars _ [] = id
subTypeVars (a:as) (t:ts) = subTypeVar a t . subTypeVars as ts

-- Collapse an application type if possible after a substitution has occured
applySort :: Type -> Sort -> Type
applySort (Inj x d as) a         = Inj x d (as ++ [a])
applySort (Sum ks as) a          = Sum ks (as ++ [a])
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
  subTypeVar a t (Inj x d as)    = Inj x d (subTypeVar a t <$> as)
  subTypeVar a t (Sum ks as)     = Sum ks (subTypeVar a t <$> as)
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
    where
      -- De-refine a type to a sort
      broaden :: Type -> Sort
      broaden (Inj _ d as)    = SData d as
      broaden (Sum ks as)     = undefined
      broaden (TVar a)        = SVar a
      broaden (t1 :=> t2)     = SArrow (broaden t1) (broaden t2)
      broaden (App t1 s2)     = (broaden t1) `applySortToSort` s2
      broaden (Lit l)         = SLit l
      broaden (Base b as)     = SData b as