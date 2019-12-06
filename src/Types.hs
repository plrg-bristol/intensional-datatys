{-# LANGUAGE FlexibleInstances, PatternSynonyms, MultiParamTypeClasses #-}

module Types (
  Guard,
  domain,
  guardStems,
  subGuard,

  Sort (SVar, SData, SArrow, SApp, SLit, SBase),
  RVar (RVar),
  Type (Var, V, Sum, Con, Dot, TVar, (:=>), App, Lit, Base),
  toType,

  DataCon (Data),

  SortScheme (SForall),
  TypeScheme (Forall), 
  tagSumsWith,

  incomparable,
  refinable,

  TypeVars (subTypeVar),
  subTypesType,
  subTypesRVar,
  subTypeVars,
  subRefinementVar,
  subRefinementVars
) where

import Control.Monad

import Data.Bifunctor
import qualified Data.List as L
import qualified Data.Map as M

import IfaceType
import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr

-- Conjunction of all side conditions that must be met for a constraint to be active
type Guard = [(Core.Name, RVar)]

domain :: Guard -> [RVar]
domain g = [x | (_, x) <- g]

guardStems :: Guard -> [Int]
guardStems g = [x | (_, RVar (x, _, _)) <- g]

subGuard :: RVar -> Type -> Guard -> Guard -> Type -> Type -> Maybe (Guard, Type, Type)
subGuard n (Sum _ _ _ cs) g g' a b = do
  guard $ all (`elem` [k' | (DataCon (k', _, _), _) <- cs]) [k | (k, n') <- g, n == n']
  return ([(k, n') | (k, n') <- g, n /= n'] <> g', a, b)
subGuard n (Var n') g g' a b = Just ([if x == n then (k, n') else (k, x) | (k, x) <- g] <> g', a, b)





-- For tracking the origin of sums, used in error messages
type Origin = Either (Core.Expr Core.Var) Core.ModuleName

-- Base sorts (unrefined types)
data Sort = 
    SVar Core.Name 
  | SData IfaceTyCon [Sort] 
  | SArrow Sort Sort 
  | SApp Sort Sort 
  | SLit Tcr.TyLit
  | SBase IfaceTyCon [Sort] -- Unrefinable datatypes
  deriving Eq

-- Refinement variables
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
  | Lit Tcr.TyLit
  | Base IfaceTyCon [Sort]

instance Eq Type where
  {-# SPECIALIZE instance Eq Type #-}
  Dot == t = True
  t == Dot = True

  Var r == Var r' = r == r'
  Sum _ tc as cs == Sum _ tc' as' cs' = tc == tc' && as == as' && all (`elem` cs') cs && all (`elem` cs) cs'
  TVar a == TVar a' = a == a'
  (t1 :=> t2) == (t1' :=> t2') = t1 == t1' && t2 == t2'
  (Lit l) == (Lit l') = l == l'
  (App t s) == (App t' s') = t == t' && s == s'

  -- Base doesn't appear in the constraint graph, this is just for comparing trivial inserts
  V x d as == Base d' as' = d == d' && as == as'
  Base d' as' == V x d as = d == d' && as == as'
  (Base tc as) == (Base tc' as') = tc == tc' && as == as'
  _ == _ = False

-- Singleton sum constructor
pattern Con :: Origin -> IfaceTyCon -> DataCon -> [Sort] -> [Type] -> Type
pattern Con e tc k as args = Sum e tc as [(k, args)]

-- Refinement variable pattern
pattern V :: Int -> IfaceTyCon -> [Sort] -> Type
pattern V x d as = Var (RVar (x, d, as))

-- Lightweight representation of Core.DataCon:
-- DataCon n as args ~~ n :: forall as . args_0 -> ... -> args_n
newtype DataCon = DataCon (Core.Name, [Core.Name], [Sort])

-- DataCons are uniquely determined by their constructor's name
instance Eq DataCon where
  {-# SPECIALIZE instance Eq DataCon #-}
  DataCon (n, _, _) == DataCon (n', _, _) = n == n'

-- DataCon constructor
pattern Data :: Core.Name -> [Core.Name] -> [Sort] -> DataCon
pattern Data n ns ss = DataCon (n, ns, ss)

-- Lift a sort to a type without taking fresh refinement variables
toType :: Sort -> Type
toType (SData d as)   = Base d as
toType (SBase d as)   = Base d as
toType (SVar a)       = TVar a
toType (SArrow s1 s2) = (toType s1) :=> (toType s2)
toType (SApp s1 s2)   = (toType s1) `applySort` s2
toType (SLit l)       = Lit l






data SortScheme = SForall [Core.Name] Sort

-- Refinement quantified sort scheme
data TypeScheme = Forall [Core.Name] [RVar] [(Guard, Type, Type)] Type

-- Associate Sum types with their module of origin
tagSumsWith :: Core.ModuleName -> TypeScheme -> TypeScheme
tagSumsWith m (Forall xs rs cs u) = Forall xs rs (fmap (bimap tagSumsWith' tagSumsWith') cs) $ tagSumsWith' u
  where
    tagSumsWith' :: Type -> Type
    tagSumsWith' (Sum _ tc ss cs) = Sum (Right m) tc ss [(d, tagSumsWith' <$> ts) | (d, ts) <- cs]
    tagSumsWith' t = t





-- Do the two types refine different sorts?
incomparable :: Type -> Type -> Bool
incomparable Dot _                       = False
incomparable _ Dot                       = False
incomparable (V _ d as) (V _ d' as')     = d /= d' || as /= as'
incomparable (V _ d as) (Sum _ d' as' _) = d /= d' || as /= as'
incomparable (V _ d as) (Base d' as')    = d /= d' || as /= as'


incomparable (Sum _ d as _) (V _ d' as')     = d /= d' || as /= as'
incomparable (Sum _ d as _) (Sum _ d' as' _) = d /= d' || as /= as'
incomparable (Sum _ d as _) (Base d' as')    = d /= d' || as /= as'

incomparable (Base d as)  (V _ d' as')     = d /= d' || as /= as'
incomparable (Base d as)  (Sum _ d' as' _) = d /= d' || as /= as'
incomparable (Base d as)  (Base d' as')    = d /= d' || as /= as'

incomparable (TVar a) (TVar a')        = a /= a'
incomparable (t1 :=> t2) (t1' :=> t2') = incomparable t1 t1' || incomparable t2 t2'
incomparable (App t s) (App t' s')     = incomparable t t' || s /= s'
incomparable (Lit l) (Lit l')          = l /= l'
incomparable _ _                       = True

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






subTypesType :: [(Type, Type)] -> Type -> Type
subTypesType  [] x = x
subTypesType  ((x, y):xys) x' | x == x'   = y
                              | otherwise = subTypesType xys x'

subTypesRVar :: [(Type, Type)] -> RVar -> Maybe RVar
subTypesRVar  [] x = Just x
subTypesRVar  ((Var x, Var y):xys) x' | x == x' = Just y
subTypesRVar  ((Var x, _):xys) x' | x == x' = Nothing
subTypesRVar  (_:xys) x = subTypesRVar xys x

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

instance TypeVars RVar Type where
  {-# SPECIALIZE instance TypeVars RVar Type #-}
  subTypeVar a t (RVar (x, d, ss)) = RVar (x, d, subTypeVar a t <$> ss)

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
    where
      -- De-refine a type to a sort
      broaden :: Type -> Sort
      broaden (V _ d as)      = SData d as
      broaden (Sum _ tc as _) = SData tc as
      broaden (TVar a)        = SVar a
      broaden (t1 :=> t2)     = SArrow (broaden t1) (broaden t2)
      broaden (App t1 s2)     = (broaden t1) `applySortToSort` s2
      broaden (Lit l)         = SLit l
      broaden (Base b as)     = SData b as

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