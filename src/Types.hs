{-# LANGUAGE PatternSynonyms #-}

module Types
    (
      Sort (SVar, SArrow, SData),
      SortScheme (SForall),
      UType (TCon, TVar, TData),
      PType,
      RVar (RVar),
      Type,
      TypeScheme (Forall),
      SExpr (V, K, (:=>)),
      ConGraph,
      upArrow,
      polarise,
      subTypeVars,
      sub,
      stems
    ) where

import GenericConGraph
import qualified DataCon as D
import qualified GhcPlugins as Core

newtype RVar = RVar (String, Bool, Core.Var) deriving Eq

instance Ord RVar where
  RVar (x, _, _) <= RVar (x', _, _) = x <= x'

data Sort = SVar Core.Var | SBase String | SData Core.Var | SArrow Sort Sort
data UType = TVar Core.Var | TBase String | TData D.DataCon | TArrow | TCon Core.Var deriving Eq
data PType = PVar Core.Var | PBase String | PData Bool Core.Var | PArrow PType PType
type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] ConGraph Type
data SortScheme = SForall [Core.Var] Sort

type ConGraph = ConGraphGen RVar UType

instance Constructor UType where
  variance TArrow = [False, True]
  variance (TCon v) = repeat True
  variance _ = []

pattern (:=>) :: Type -> Type -> Type
pattern t1 :=> t2 = Con TArrow [t1, t2]

pattern K :: Core.Var -> [Type] -> Type
pattern K v ts = Con (TCon v) ts

pattern V :: String -> Bool -> Core.Var -> Type
pattern V x p d = Var (RVar (x, p, d))

stems :: Type -> [String]
stems (V x _ _) = [x]
stems (Con c cargs) = concatMap stems cargs
stems (Sum cs) = concatMap (\(_, cargs) -> concatMap stems cargs) cs
stems _ = []

upArrow :: String -> [PType] -> [Type]
upArrow x = fmap upArrow'
  where
    upArrow' (PData p d)     = Var $ RVar (x, p, d)
    upArrow' (PArrow t1 t2)  = Con TArrow [upArrow' t1, upArrow' t1]
    upArrow' (PVar a)        = Con (TVar a) []
    upArrow' (PBase b)       = Con (TBase b) []

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b) = PBase b
polarise p (SData d) = PData p d
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)

sub :: [RVar] -> [Type] -> Type -> Type
sub _ _ Zero = Zero
sub _ _ One = One
sub [] _ t = t
sub _ [] t = t
sub (x:xs) (y:ys) (Var x')
  | x == x' = y
  | otherwise = sub xs ys (Var x')
sub xs ys (Con c cargs) = Con c $ fmap (sub xs ys) cargs
sub xs ys (Sum cs) = Sum $ fmap (\(c, cargs) -> (c, fmap (sub xs ys) cargs)) cs

subTypeVars :: [Core.Var] -> [Type] -> Type -> Type
subTypeVars [] _ u = u
subTypeVars _ [] u = u
subTypeVars (a:as) (t:ts) (Con (TVar a') [])
  | a == a' = subTypeVars as ts t
  | otherwise = subTypeVars as ts $ Con (TVar a') []
subTypeVars (a:as) (t:ts) (Sum [(TVar a', [])])
  | a == a' = subTypeVars as ts t
  | otherwise = subTypeVars as ts $ Con (TVar a') []
subTypeVars (a:as) (t:ts) t' = subTypeVars as ts t'
