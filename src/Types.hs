{-# LANGUAGE PatternSynonyms #-}

module Types
    (
      Sort (SVar, SArrow, SData, SBase),
      SortScheme (SForall),
      UType (TVar, TData, TArrow, TBase),
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
import qualified GhcPlugins as Core
import Debug.Trace

newtype RVar = RVar (String, Bool, Core.TyCon) deriving (Show, Eq)

instance Ord RVar where
  RVar (x, _, _) <= RVar (x', _, _) = x <= x'

data Sort = SVar Core.Var | SBase Core.TyCon | SData Core.TyCon | SArrow Sort Sort deriving Show
data UType = TVar Core.Var | TBase Core.TyCon | TData Core.DataCon | TArrow deriving Show
data PType = PVar Core.Var | PBase Core.TyCon | PData Bool Core.TyCon | PArrow PType PType
type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] ConGraph Type deriving Show
data SortScheme = SForall [Core.Var] Sort

instance Eq UType where
  TVar x == TVar y = Core.getName x == Core.getName y
  TBase b == TBase b' = Core.getName b == Core.getName b'
  TData d == TData d' = Core.getName d == Core.getName d'
  TArrow == TArrow = True
  _ == _ = False

type ConGraph = ConGraphGen RVar UType

instance Show Core.Var where
  show = Core.nameStableString . Core.getName

instance Show Core.Name where
  show = Core.nameStableString

instance Show Core.TyCon where
  show = Core.nameStableString . Core.getName

instance Show Core.DataCon where
  show = Core.nameStableString . Core.getName

instance Constructor UType where
  variance TArrow = [False, True]
  variance _ = repeat True

pattern (:=>) :: Type -> Type -> Type
pattern t1 :=> t2 = Con TArrow [t1, t2]

pattern K :: Core.DataCon -> [Type] -> Type
pattern K v ts = Con (TData v) ts

pattern V :: String -> Bool -> Core.TyCon -> Type
pattern V x p d = Var (RVar (x, p, d))

stems :: Type -> [String]
stems (V x _ _) = [x]
stems (Sum cs) = concatMap (\(_, cargs) -> concatMap stems cargs) cs
stems _ = []

upArrow :: String -> [PType] -> [Type]
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

subTypeVars :: [Core.Var] -> [Type] -> Type -> Type
subTypeVars [] [] u = u
-- subTypeVars (a:as) (t:ts) (Con (TVar a') [])
--   | a == a' = subTypeVars as ts t
--   | otherwise = subTypeVars as ts $ Con (TVar a') []
-- subTypeVars (a:as) (t:ts) (Sum cs) = subTypeVars as ts $ (fmap subtv' cs)
--   where
--     subtv' :: (UType, [Type]) -> (UType, [Type])
--     subtv' (c, cargs)
--       | c == TVar a = t
subTypeVars _ _  _ = error "Substitution vectors have different lengths"
