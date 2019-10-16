{-# LANGUAGE FlexibleInstances #-}

module Types where

import Data.Maybe
import Data.List
import Data.Map.Strict as Map hiding (map)

infixr :=>
data Type = TVar String | TBase String | TData String | RVar String Bool String | Type :=> Type | Sum [Constructor] deriving (Ord, Eq)

-- Polarised type
data PType = PVar String | PBase String | PData Bool String | PArrow PType PType deriving (Show, Ord, Eq)

data Sort = SVar String | SBase String | SData String | SArrow Sort Sort

instance Show Sort where
  show (SVar v) = v
  show (SBase b) = b
  show (SData d) = d
  show (SArrow t1 t2) = "(" ++ show t1 ++ "->" ++ show t2 ++ ")"

data SortScheme = SForall [String] Sort

instance Show SortScheme where
  show (SForall as s) = "forall " ++ intercalate " " as ++ "." ++ show s

instance Show Type where
  show (TVar v) = v
  show (TBase b) = b
  show (TData d) = d
  show (t1 :=> t2) = "(" ++ show t1 ++ "->" ++ show t2 ++ ")"
  show (RVar x p d) = "(" ++ x ++ "!" ++ (if p then "+" else "-") ++ d ++ ")"
  show (Sum ks) = "(" ++ intercalate "+" (map show ks) ++ ")"

data Constructor = Constructor String [Type] deriving (Ord, Eq, Show)

isConstructor :: Type -> Bool
isConstructor (Sum [k]) = True
isConstructor _ = False

upArrow :: String -> [PType] -> [Type]
upArrow x = map upArrow'
  where
    upArrow' (PData p d)     = RVar x p d
    upArrow' (PArrow t1 t2)  = upArrow' t1 :=> upArrow' t2
    upArrow' (PVar a)        = TVar a
    upArrow' (PBase b)       = TBase b

class Sub a where
    sub :: Map String Type -> Map (String, Bool, String) Type -> a -> a

instance Sub Type where
    sub tv _ t@(TVar s) = fromMaybe t (tv !? s)
    sub _ _ (TBase b) = TBase b
    sub _ _ (TData d) = TData d
    sub _ rm t@(RVar s p d) = fromMaybe t (rm !? (s, p, d))
    sub tv rv (t1 :=> t2) = sub tv rv t1 :=> sub tv rv t2
    sub tv rv (Sum cons) = Sum [Constructor k $ sub tv rv args | Constructor k args <- cons]

instance (Functor f, Sub a) => Sub (f a) where
    sub tv tr as = fmap (sub tv tr) as
