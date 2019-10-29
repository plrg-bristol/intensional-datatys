{-# LANGUAGE PatternSynonyms, TypeSynonymInstances, FlexibleInstances #-}

module Types
    (
      Sort (SVar, SArrow, SData, SBase),
      SortScheme (SForall),
      UType (TVar, TData, TArrow, TBase, TLit),
      PType,
      RVar (RVar),
      Type,
      TypeScheme (Forall),
      SExpr (V, K, B, (:=>)),
      ConGraph,
      upArrow,
      polarise,
      subTypeVars,
      subSortVars,
      sub,
      stems
    ) where

import Prelude hiding ((<>))
import Data.List
import GenericConGraph
import qualified GhcPlugins as Core
import Debug.Trace
import Outputable

newtype RVar = RVar (Int, Bool, Core.TyCon) deriving Eq

instance Ord RVar where
  RVar (x, _, _) <= RVar (x', _, _) = x <= x'

data Sort = SVar Core.Var | SBase Core.TyCon | SData Core.TyCon | SArrow Sort Sort
data UType = TVar Core.Var | TBase Core.TyCon | TData Core.DataCon | TArrow | TLit Core.Literal -- Sums can contain literals
data PType = PVar Core.Var | PBase Core.TyCon | PData Bool Core.TyCon | PArrow PType PType
type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] ConGraph Type
data SortScheme = SForall [Core.Var] Sort

instance Core.Outputable UType where
  ppr (TVar v) = ppr v
  ppr (TBase b) = ppr b
  ppr (TData dc) = ppr dc

instance Core.Outputable RVar where
  ppr (RVar (x, p, d)) = (text "[") <> (ppr x) <> (if p then text"+" else text "-") <> ppr d <> text "]"

instance Core.Outputable Type where
  ppr (V x p d) = text "[" <> (ppr x) <> (if p then (text "+") else text "-") <> ppr d <>  text "]"
  ppr (t1 :=> t2) =  text "(" <> (ppr t1) <>  text "->" <> (ppr t2) <>  text ")"
  ppr (K v ts) = ppr v <>  text "(" <> interpp'SP ts <>  text ")"
  ppr (Sum cs) = pprWithBars (\(c, cargs) -> ppr c <>  text "(" <> interpp'SP cargs <> text ")") cs

instance Core.Outputable TypeScheme where
  ppr (Forall as xs cg t) = text "∀" <> interppSP as <> text ".∀"  <> interppSP xs <> text "." <> ppr t <> text "where:" <> interppSP (toList cg)

instance Eq UType where
  TVar x == TVar y = Core.getName x == Core.getName y
  TBase b == TBase b' = Core.getName b == Core.getName b'
  TData d == TData d' = Core.getName d == Core.getName d'
  TLit l == TLit l' = l == l'
  TArrow == TArrow = True
  _ == _ = False

type ConGraph = ConGraphGen RVar UType

instance Core.Outputable ConGraph where
  ppr (ConGraph{succs = s, preds = p, subs =sb}) = ppr s <> text "\n" <> ppr p <> text "\n" -- <> (text $ show sb)

split :: String -> [String]
split [] = [""]
split (c:cs) | c == '$'  = "" : rest
             | otherwise = (c : head rest) : tail rest
    where rest = split cs

-- instance Show Core.Var where
--   show n = last $ split (Core.nameStableString $ Core.getName n)
--
-- instance Show Core.Name where
--   show n = last $ split (Core.nameStableString $ Core.getName n)
--
-- instance Show Core.TyCon where
--   show n = last $ split (Core.nameStableString $ Core.getName n)
--
-- instance Show Core.DataCon where
--   show n = last $ split (Core.nameStableString $ Core.getName n)

instance Constructor UType where
  variance TArrow = [False, True]
  variance _ = repeat True

pattern (:=>) :: Type -> Type -> Type
pattern t1 :=> t2 = Con TArrow [t1, t2]

pattern K :: Core.DataCon -> [Type] -> Type
pattern K v ts = Con (TData v) ts

pattern V :: Int -> Bool -> Core.TyCon -> Type
pattern V x p d = Var (RVar (x, p, d))

pattern B :: Core.TyCon -> Type
pattern B b = Con (TBase b) []

stems :: Type -> [Int]
stems (V x _ _) = [x]
stems (Sum cs) = concatMap (\(_, cargs) -> concatMap stems cargs) cs
stems _ = []

upArrow :: Int -> [PType] -> [Type]
upArrow x = fmap upArrow'
  where
    upArrow' (PData p d)     = Var $ RVar (x, p, d)
    upArrow' (PArrow t1 t2)  = upArrow' t1 :=> upArrow' t2
    upArrow' (PVar a)        = Con (TVar a) []
    upArrow' (PBase b)       = Con (TBase b) []

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b) = PBase b
polarise p (SData d) = PData p d
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)

sub :: [RVar] -> [Type] -> Type -> Type
sub [] [] t = t
sub (x:xs) (y:ys) (Var x')
  | x == x' = y
  | otherwise = sub xs ys (Var x')
sub xs ys (Sum cs) = Sum $ fmap (\(c, cargs) -> (c, fmap (sub xs ys) cargs)) cs
sub _ _ _ = error "Substitution vectors have different lengths"

subSortVars :: [Core.Var] -> [Sort] -> Sort -> Sort
subSortVars [] [] u = u
subSortVars (a:as) (t:ts) (SVar a')
  | a == a' = subSortVars as ts t
  | otherwise = subSortVars as ts (SVar a')
subSortVars as ts (SArrow s1 s2) = SArrow (subSortVars as ts s1) (subSortVars as ts s2)
subSortVars _ _ s = s

subTypeVars :: [Core.Var] -> [Type] -> Type -> Type
subTypeVars [] [] u = u
subTypeVars (a:as) (t:ts) (Con (TVar a') [])
  | a == a' = subTypeVars as ts t
  | otherwise = subTypeVars as ts $ Con (TVar a') []
subTypeVars as ts (Sum ((c, cargs):cs)) = let
  Sum cs' = subTypeVars as ts (Sum cs)
  in Sum $ (c, fmap (subTypeVars as ts) cargs):cs'
subTypeVars as ts (Var v) = Var v -- Type and refinement variables are orthogonal
subTypeVars as ts One = One
subTypeVars as ts Zero = Zero
