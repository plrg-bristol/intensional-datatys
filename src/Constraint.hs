{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

module Constraint (
  K(..),
  pattern Con,
  Guard,

  ConSet,
  fromList,
  toList,
  singleton,
  insert,
  guardWith,

  TypeScheme(..),
  simple,

  resolve
) where

import qualified Data.List as L
import qualified Data.Map as M

import Outputable
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core hiding ((<>))

import Types

-- Constructors set
data K where
  Dom :: Int -> Core.Name -> K
  Set :: [Core.Name] -> K
  deriving Eq

pattern Con :: Core.Name -> K
pattern Con d = Set [d]

-- Internal (atomic) constraint
data Constraint where
  DomDom :: Int -> Int -> Core.Name -> Constraint
  ConDom :: Core.Name -> Int -> Core.Name -> Constraint
  DomSet :: Int -> Core.Name -> [Core.Name] -> Constraint
  deriving (Eq, Ord)

instance Refined Constraint where
  domain (DomDom x y _) = [x, y]
  domain (ConDom _ x _) = [x]
  domain (DomSet x _ _) = [x]

  rename x y (DomDom x' x'' d)
    | x == x'  = DomDom y x'' d
    | x == x'' = DomDom x' y d
  rename x y (ConDom k x' d)
    | x == x' = ConDom k y d
  rename x y (DomSet x' d ks)
    | x == x' = DomSet y d ks
  rename _ _ c = c

-- Atomic constraints behave like a ordered pair of constructor sets
lhs :: Constraint -> K
lhs (DomDom x _ d) = Dom x d
lhs (ConDom k _ _) = Set [k]
lhs (DomSet x d _) = Dom x d

rhs :: Constraint -> K
rhs (DomDom _ y d) = Dom y d
rhs (ConDom _ x d) = Dom x d
rhs (DomSet _ _ k) = Set k

-- Convert a pair of constructor sets to atomic form if possible
toAtomic :: K -> K -> [Constraint]
toAtomic (Dom x d) (Dom y d')
  | d /= d'   = Core.pprPanic "Invalid subtyping constraint!" (Core.ppr (d, d'))
  | x == y    = []
  | otherwise = [DomDom x y d]
toAtomic (Dom x d) (Set k)  = [DomSet x d k]
toAtomic (Set ks) (Dom x d) = fmap (\k -> ConDom k x d) ks






-- A guard is a conjunction of k in dom(X(d), grouped as X |-> (k, d)
newtype Guard = Guard (M.Map Int [(Core.Name, Core.Name)])

instance Eq Guard where
  g == g' = g `subsume` g' && g' `subsume` g

-- Is the first guard weaker than the second?
subsume :: Guard -> Guard -> Bool
subsume (Guard m) (Guard m') = M.foldrWithKey pred True m'
  where
    pred x ps k =
      case M.lookup x m of
        Just ps' -> all (`elem` ps') ps  -- every constraint of X in m' should appear in m 
        Nothing  -> null ps && k         -- m does not constrain X, neither should m'

instance Semigroup Guard where
  Guard m <> Guard m' = Guard (m `M.union` m')

instance Monoid Guard where
  mempty = Guard M.empty

instance Refined Guard where
  domain (Guard m) = M.keys m

  rename x y (Guard m) = Guard $ M.mapKeys (\x' -> if x == x' then y else x') m

-- Potentially add a new guard or subsumed an existing guard
mergeGuards :: Guard -> [Guard] -> [Guard]
mergeGuards g [] = [g]
mergeGuards g (g':gs)
  | g  `subsume` g' = mergeGuards g' gs
  | g' `subsume` g  = mergeGuards g gs
  | otherwise       = g' : mergeGuards g gs






-- A collection of guarded constraints    
newtype ConSet = ConSet (M.Map Constraint [Guard])

instance Eq ConSet where
  ConSet m == ConSet m' = M.isSubmapOfBy perm m m' && M.isSubmapOfBy perm m' m
    where
      perm :: Eq a => [a] -> [a] -> Bool
      perm xs ys = null (ys L.\\ xs) && null (xs L.\\ ys)

instance Semigroup ConSet where
  ConSet m <> ConSet m' = ConSet $ M.unionWith (foldr mergeGuards) m m'

instance Monoid ConSet where
  mempty = ConSet M.empty

instance Refined ConSet where
  domain (ConSet m)     = concatMap domain (M.keys m) ++ concatMap (concatMap domain) (M.elems m)
  rename x y (ConSet m) = ConSet $ M.mapKeys (rename x y) $ M.map (map $ rename x y) m

-- Insert an atomic constraint, combining with existing guards 
insertAtomic :: Constraint -> Guard -> ConSet -> ConSet
insertAtomic c g (ConSet cs) = ConSet $ M.insertWith (foldr mergeGuards) c [g] cs

-- Insert any constructor set constraint
insert :: K -> K -> Guard -> ConSet -> ConSet
insert k1 k2 g cs = foldr (`insertAtomic` g) cs (toAtomic k1 k2)

-- Build a atomic constraint set from a list
fromList :: [(K, K, Guard)] -> ConSet
fromList [] = mempty
fromList ((k1, k2, g):cs) = insert k1 k2 g (fromList cs)

-- Inverse of fromList
toList :: ConSet -> [(K, K, Guard)]
toList (ConSet m) = [(lhs c, rhs c, g) | (c, gs) <- M.toList m, g <- gs]

-- A single constraint
singleton :: K -> K -> Guard -> ConSet
singleton k1 k2 g = insert k1 k2 g mempty

-- Add a guard to the entire set
guardWith :: Core.Name -> Int -> Core.Name -> ConSet -> ConSet
guardWith k x d (ConSet cs) = ConSet $ M.map (mergeGuards $ Guard $ M.singleton x [(k, d)]) cs

-- Filter a constraint set to a certain domain
restrict :: [Int] -> ConSet -> ConSet
restrict xs (ConSet m) = ConSet $ M.filterWithKey (const . (all (`elem` xs) . domain)) $ filter (all (`elem` xs) . domain) <$> m




-- Constraint quantified type scheme
newtype TypeScheme = TypeScheme ([Int], ConSet, Type T)

simple :: Type T -> TypeScheme
simple t = TypeScheme ([], mempty, t)





return' :: Constraint -> Guard -> ConSet
return' c g = insertAtomic c g mempty

bind :: ConSet -> (Constraint -> Guard -> ConSet) -> ConSet
bind (ConSet m) f = M.foldrWithKey (\c gs m' -> foldr (\g-> (f c g Prelude.<>)) m' gs) mempty m

-- Close a constrain set under resolve
resolve :: [Int] -> ConSet -> ConSet
resolve xs = restrict xs . resolve'
  where
    resolve' cs
      | cross xs cs == cs = cs
      | otherwise         = resolve' (cross xs cs)

-- Apply the resolution rules once
cross :: [Int] -> ConSet -> ConSet
cross xs cs = cs `bind` (\c g -> cs `bind` (\c' g' -> trans c' g' c g Prelude.<> 
                                                      trans c g c' g' Prelude.<> 
                                                      weak c' g' c g Prelude.<> 
                                                      weak c g c' g' Prelude.<> 
                                                      return' c g Prelude.<> 
                                                      return' c' g'))
  where
    trans :: Constraint -> Guard -> Constraint -> Guard -> ConSet
    trans c g c' g'
      | any (`notElem` xs) (domain c ++ domain g ++ domain c' ++ domain g') = mempty 
      | rhs c == lhs c' = insert (lhs c) (rhs c') (g Prelude.<> g') mempty
    trans _ _ _ _ = mempty

    weak :: Constraint -> Guard -> Constraint -> Guard -> ConSet
    weak c@(ConDom k x d) g c' (Guard g')
      | any (`notElem` xs) (domain c ++ domain g ++ domain c' ++ domain (Guard g')) = mempty 
      | Just kds <- M.lookup x g'
      , (k, d) `elem` kds = return' c' (Guard $ M.adjust (L.delete (k, d)) x g')
    weak _ _ _ _ = mempty
  
instance Outputable Guard where
  ppr (Guard g) = ppr (M.toList g)

instance Outputable K where
  ppr (Dom x d) = sep [text "inj", ppr x, ppr d]
  ppr (Set ks)  = pprWithBars ppr ks

instance Outputable ConSet where
  ppr cs = vcat (map ppr (toList cs))

instance Outputable TypeScheme where
  ppr (TypeScheme (xs, cs, t)) = hang (text "forall" <+> fsep (map ppr xs) Outputable.<> dot Outputable.<> ppr t)
                                    2 (ppr cs)