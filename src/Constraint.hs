{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternSynonyms #-}

module Constraint (
  K(..),
  pattern Con,

  Guard,
  top,

  ConSet,
  empty,
  union,
  insert,
  --fromList,
  --toList,
  guardWith,

  resolve
) where

import Prelude hiding ((<>), and)

import qualified Data.List as L
import qualified Data.Map as M

import Outputable hiding (empty)
import qualified Pretty as Pretty
import qualified GhcPlugins as Core

import Types

-- Constructors set
data K where
  Dom :: Int -> Core.Name -> K
  Set :: [Core.Name] -> K
  deriving Eq

pattern Con :: Core.Name -> K
pattern Con d = Set [d]

instance Outputable K where
  ppr (Dom x d) = text "dom" <> parens (ppr x <> parens (ppr d))
  ppr (Set ks)  = pprWithBars ppr ks

subset :: K -> K -> Bool
subset (Dom x d) (Dom x' d') = x == x' && d == d'
subset (Set ks) (Set ks')    = all (`elem` ks') ks
subset _ _                   = False

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

instance Outputable Constraint where
  ppr c = ppr (lhs c) <+> arrowt <+> ppr (rhs c)

-- Atomic constraints behave like a ordered pair of constructor sets
lhs :: Constraint -> K
lhs (DomDom x _ d) = Dom x d
lhs (ConDom k _ _) = Con k
lhs (DomSet x d _) = Dom x d

rhs :: Constraint -> K
rhs (DomDom _ y d) = Dom y d
rhs (ConDom _ x d) = Dom x d
rhs (DomSet _ _ k) = Set k

toAtomic :: K -> K -> [Constraint]
toAtomic (Dom x d) (Dom y d')
  | d /= d'   = Core.pprPanic "Invalid subtyping constraint!" (Core.ppr (d, d'))
  | x == y    = []
  | otherwise = [DomDom x y d]
toAtomic (Dom x d) (Set k)  = [DomSet x d k]
toAtomic (Set ks) (Dom x d) = fmap (\k -> ConDom k x d) ks
toAtomic (Set ks) (Set ks')
  | all (`elem` ks') ks = []
  | otherwise           = Core.pprPanic "Invalid subtyping constraint!" (Core.ppr (ks, ks'))






-- A guard is a conjunction of k in dom(X(d) {grouped as X |-> (k, d)}
newtype Guard = Guard (M.Map Int [(Core.Name, Core.Name)])
  deriving Eq

instance Refined Guard where
  domain (Guard m) = M.keys m
  rename x y (Guard m) = Guard $ M.mapKeys (\x' -> if x == x' then y else x') m

instance Outputable Guard where
  ppr (Guard g) = sep (punctuate and [dom (x, k) | (x, ks) <- M.toList g, k <- ks])
    where
      dom (x, (k, d)) = ppr k <+> char '∈' <+> ppr (Dom x d)
      elem = unicodeSyntax (char '∈') (docToSDoc $ Pretty.text "in")
      and  = unicodeSyntax (char '∧') (docToSDoc $ Pretty.text "&&")

-- Trivially true guard
top :: Guard
top = Guard $ M.empty

-- Guard generator
dom :: Core.Name -> Int -> Core.Name -> Guard
dom k x d = Guard $ M.singleton x [(k, d)]

-- Conjunction of guards
and :: Guard -> Guard -> Guard
and (Guard m) (Guard m') = Guard $ M.unionWith (L.union) m m'

-- Remove a conjunction from a guard
remove :: Core.Name -> Int -> Core.Name -> Guard -> Guard
remove k x d (Guard m) = Guard $ M.adjust (L.delete (k, d)) x m

-- Is the first guard as strong as than the second?
entails :: Guard -> Guard -> Bool
entails (Guard m) (Guard m') = M.foldrWithKey pred True m'
  where
    pred x ps k = k &&
      case M.lookup x m of
        Just ps' -> all (`elem` ps') ps
        Nothing  -> null ps

-- Potentially add a new guard to list of alternatives or subsumed an existing guard
mergeGuards :: Guard -> [Guard] -> [Guard]
mergeGuards g [] = [g]
mergeGuards g (g':gs)
  | g' `entails` g = mergeGuards g gs
  | otherwise      = g' : mergeGuards g gs






-- A collection of guarded constraints    
newtype ConSet = ConSet (M.Map Constraint [Guard])
  deriving Eq

-- TODO: inline this
-- instance Eq ConSet where
--   c == c' = leq (toList c) (toList c') && leq (toList c') (toList c)
--     where
--       leq l = all (\(k1, k2, g) -> any (\(k1', k2', g') -> entails g g' && subset k2' k2 && subset k1 k1') l)

instance Refined ConSet where
  domain (ConSet m)     = L.nub (concatMap domain (M.keys m) ++ concatMap (concatMap domain) (M.elems m))
  rename x y (ConSet m) = ConSet $ M.mapKeys (rename x y) $ M.map (map $ rename x y) m

instance Outputable ConSet where
  ppr cs = vcat [(if M.null m then Core.empty else ppr g <+> char '?') <+> ppr k1 <+> arrowt <+> ppr k2 | (k1, k2, g@(Guard m)) <- toList cs]

-- Empty set of constraints
empty :: ConSet
empty = ConSet $ M.empty

-- Combined constraint sets
union :: ConSet -> ConSet -> ConSet
union (ConSet cs) (ConSet cs') = ConSet $ M.union cs cs'

-- Insert an atomic constraint, combining with existing guards 
insertAtomic :: Constraint -> Guard -> ConSet -> ConSet
insertAtomic c g (ConSet cs) = ConSet $ M.insertWith (foldr mergeGuards) c [g] cs

-- Insert any constructor set constraint
insert :: K -> K -> Guard -> ConSet -> ConSet
insert k1 k2 g cs = foldr (`insertAtomic` g) cs (toAtomic k1 k2)

-- ConSet behaves like [(K, K, Guard)]
fromList :: [(K, K, Guard)] -> ConSet
fromList []               = ConSet $ M.empty
fromList ((k1, k2, g):cs) = insert k1 k2 g (fromList cs)

toList :: ConSet -> [(K, K, Guard)]
toList (ConSet m) = [(lhs c, rhs c, g) | (c, gs) <- M.toList m, g <- gs]

-- Add a guard to an entire set
guardWith :: Core.Name -> Int -> Core.Name -> ConSet -> ConSet
guardWith k x d (ConSet cs) = ConSet $ M.map (fmap $ and (Guard $ M.singleton x [(k, d)])) cs

-- Filter a constraint set to a certain domain
restrict :: [Int] -> ConSet -> ConSet
restrict xs (ConSet m) = ConSet $ M.filterWithKey (const . (all (`elem` xs) . domain))
                                $ filter (all (`elem` xs) . domain)
                               <$> m







-- Atomic singleton
return' :: Constraint -> Guard -> ConSet
return' c g = ConSet $ M.singleton c [g]

-- Apply the function to every constraint and union the results
bind :: ConSet -> (Constraint -> Guard -> ConSet) -> ConSet
bind (ConSet m) f = M.foldrWithKey (\c gs cs -> foldr (\g cs' -> f c g `union` cs') cs gs) empty m

-- Close a constrain set under resolve'
resolve :: [Int] -> ConSet -> ConSet
resolve xs = restrict xs . resolve'
  where
    resolve' cs
      | cross xs cs == cs = cs
      | otherwise         = resolve' (cross xs cs)

-- Apply the resolution rules once
cross :: [Int] -> ConSet -> ConSet
cross xs cs = cs `bind` (\c g -> cs `bind` (\c' g' -> trans c' g' c  g  `union`
                                                      trans c  g  c' g' `union`
                                                      weak  c' g' c  g  `union`
                                                      weak  c  g  c' g' `union`
                                                      return'     c  g  `union`
                                                      return'     c' g'))
  where
    -- Transitive closure
    trans :: Constraint -> Guard -> Constraint -> Guard -> ConSet
    trans c g c' g'
      -- | all (`elem` xs) (domain c ++ domain c') -- Both sides are relevant
      | rhs c == lhs c' = insert (lhs c) (rhs c') (g `and` g') empty
    trans _ _ _ _       = empty

    -- Weakening rule
    weak :: Constraint -> Guard -> Constraint -> Guard -> ConSet
    weak c@(ConDom k x d) g c' g'@(Guard m)
      -- | all (`elem` xs) (domain c ++ domain c' ++ domain g') -- Both sides are relevant
      | Just kds <- M.lookup x m
      , (k, d) `elem` kds = return' c' (g `and` (remove k x d g'))
    weak _ _ _ _          = empty