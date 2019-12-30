{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleInstances #-}

module Constraint (
  Constraint(..),
  K (..),
  pattern Con,
  Guard (..),
  ConSet,
  insertS,
  insertT,
  insertA,
  resolve,
  domain,
  filterToSet,
) where

import Prelude

import qualified Data.List as L
import qualified Data.Map as M

import qualified GhcPlugins as Core

import Utils
import Types

-- Internal (atomic) constraint rep
data Constraint where
  DomDom :: Int -> Int -> Core.Name -> Constraint
  ConDom :: Core.Name -> Int -> Core.Name -> Constraint
  DomSet :: Int -> Core.Name -> [Core.Name] -> Constraint
  deriving (Eq, Ord)

instance Rename Constraint where
  rename x y (DomDom x' x'' d)
    | x == x'  = DomDom y x'' d 
    | x == x'' = DomDom x' y d
  rename x y (ConDom k x' d)
    | x == x'  = ConDom k y d
  rename x y (DomSet x' d ks)
    | x == x'  = DomSet y d ks

-- Sets of constructors 
data K where
  Dom :: Int -> Core.Name -> K
  Set :: [Core.Name] -> K
  deriving Eq

pattern Con :: Core.Name -> K
pattern Con d = Set [d]

lhs :: Constraint -> K
lhs (DomDom x _ d) = Dom x d
lhs (ConDom k _ _) = Set [k]
lhs (DomSet x d _) = Dom x d

rhs :: Constraint -> K
rhs (DomDom _ y d) = Dom y d
rhs (ConDom _ x d) = Dom x d
rhs (DomSet _ _ k) = Set k

domainC :: Constraint -> [Int]
domainC (DomDom x y d) = [x, y]
domainC (ConDom k x d) = [x]
domainC (DomSet x d ks) = [x]

-- Convert a pair of constructor sets to atomic form if possible
toAtomic :: K -> K -> [Constraint]
toAtomic (Dom x d) (Dom y d')
  | d == d'   = [DomDom x y d]
  | otherwise = Core.pprPanic "Invalid subtyping constraint!" (Core.ppr (d, d'))
toAtomic (Dom x d) (Set k)   = [DomSet x d k]
toAtomic (Set ks) (Dom x d)  = fmap (\k -> ConDom k x d) ks






-- A guard is a conjunction of k in dom(X(d), grouped as X |-> (k, d)
newtype Guard = Guard (M.Map Int [(Core.Name, Core.Name)])
  deriving Eq

instance Semigroup Guard where
  (Guard m) <> (Guard m') = Guard (M.union m m')

instance Monoid Guard where
  mempty = Guard M.empty 

-- X <= Y if X -> Y
instance Ord Guard where
  Guard m <= Guard m' = M.foldrWithKey pred True m'
    where
      pred :: Int -> [(Core.Name, Core.Name)] -> Bool -> Bool
      pred x ps k =
        case M.lookup x m of
          Just ps' -> all (`elem` ps') ps  -- every constraint of X in m' should appear in m 
          Nothing  -> null ps && k         -- m does not constrain X, so neither should m'

instance Rename Guard where
  rename x y (Guard m) = Guard (M.mapKeys r m)
    where
      r x'
        | x == x'    = y
        | otherwise  = x'

-- Potentially add a new guard or subsumed an existing guard
mergeGuards :: Guard -> [Guard] -> [Guard]
mergeGuards g = foldr go [g]
  where
    go g' gs
      | g <= g'   = gs
      | otherwise = L.insert g' gs

domainG :: Guard -> [Int]
domainG (Guard m) = M.keys m






-- A collection of guarded constraints    
type ConSet = M.Map Constraint [Guard]

instance Rename ConSet where
  rename x y = M.mapKeys (rename x y) . M.map (fmap $ rename x y)

domain :: ConSet -> [Int]
domain m = concatMap domainC (M.keys m) ++ concatMap domainG (concat (M.elems m))

-- Insert an atomic constraint, combining with existing guards 
insertA :: Constraint -> Guard -> ConSet -> ConSet
insertA c g = M.insertWith (foldr mergeGuards) c [g]

-- Insert a subset constraint
insertS :: K -> K -> Guard -> ConSet -> ConSet
insertS k1 k2 g cs = foldr (`insertA` g) cs (toAtomic k1 k2)

-- Insert a subtyping constraint
insertT :: Type e -> Type e -> Guard -> ConSet -> Core.Expr Core.Var -> ConSet
insertT t1 t2 g cs e = foldr (`insertA` g) cs (simplify t1 t2 e)

-- Convert subtyping constraints to constructor constraints (if they have the same underlying sort)
simplify :: Type e -> Type e -> Core.Expr Core.Var -> [Constraint]
simplify t1 t2 e 
  | shape t1 /= shape t2               = Core.pprPanic "Types must refine the same sort!" (Core.ppr (t1, t2, e))
simplify (t11 :=> t12) (t21 :=> t22) e = simplify t21 t11 e `L.union` simplify t12 t22 e
simplify (Inj x d) (Inj y _) e         = DomDom x y . Core.getName <$> slice d
simplify _ _ _                         = []

-- Combine two constraint sets
union :: ConSet -> ConSet -> ConSet
union = M.unionWith $ foldr mergeGuards






return' :: Constraint -> Guard -> ConSet
return' c g = insertA c g M.empty

bind :: ConSet -> (Constraint -> Guard -> ConSet) -> ConSet
bind m f = M.foldrWithKey (\c gs m' -> foldr (M.unionWith (foldr mergeGuards) . f c) m' gs) M.empty m

-- Close a constrain set under resolve
resolve :: ConSet -> ConSet
resolve cs
  | trans cs == cs = cs
  | otherwise      = resolve (trans cs)

-- Apply the transitive closure opperation once
trans :: ConSet -> ConSet
trans xs = xs `bind` (\c v -> xs `bind` cross c v)
  where
    --Todo apply both cases at once
    cross :: Constraint -> Guard -> Constraint -> Guard -> ConSet
    cross c@(ConDom k x d) g c' (Guard g')
      | Just kds <- M.lookup x g'
      , (k, d) `elem` kds = insertA c g $ return' c' $ Guard (M.adjust (L.delete (k, d)) x g')
    cross c g c' g'
      | rhs c == lhs c'   = insertA c g $ insertS (lhs c) (rhs c') (g <> g') $ return' c' g'
    cross c g c' g'       = insertA c g $ return' c' g'

-- Remove intermediate nodes
filterToSet :: [Int] -> ConSet -> ConSet
filterToSet xs cs = M.filterWithKey (\k _ -> all (`elem` xs) (domainC k)) $ M.map (filter (\(Guard g) -> all (`elem` xs) (M.keys g))) cs
