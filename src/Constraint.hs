{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Constraint (
  K(..),
  con,
  set,

  Guard,
  top,

  ConSet,
  empty,
  insert,
  union,
  guardWith,
  saturate,
) where

import Prelude hiding ((<>), and)

import UniqSet
import qualified Data.Map as M
import qualified Data.Set as S

import Outputable hiding (empty)
import qualified Pretty as Pretty
import qualified GhcPlugins as Core

import Types

-- General constructors set
data K where
  Dom :: Int -> Core.Name -> K
  Set :: UniqSet Core.Name -> K
  deriving Eq

instance Refined K where
  domain (Dom x _) = [x]
  domain (Set _)   = []

  rename x y (Dom x' d)
    | x == x'  = Dom y d
  rename _ _ c = c

instance Outputable K where
  ppr (Dom x d)       = text "dom" <> parens (ppr x <> parens (ppr d))
  ppr (Set ks)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (docToSDoc $ Pretty.text "{}")
    | otherwise         = pprWithBars ppr (nonDetEltsUniqSet ks)

-- Convenient smart constructors
con :: Core.Name -> K
con = Set . unitUniqSet

set :: [Core.Name] -> K
set = Set . mkUniqSet

-- Is the first constructor set a susbet of the second
subset :: K -> K -> Bool
subset (Dom x d) (Dom x' d') = x == x' && d == d'
subset (Set ks) (Set ks')    = uniqSetAll (`elementOfUniqSet` ks) ks'
subset _ _                   = False






-- Internal (atomic) constraint
data Constraint where
  DomDom :: Int -> Int -> Core.Name -> Constraint
  ConDom :: Core.Name -> Int -> Core.Name -> Constraint
  DomSet :: Int -> Core.Name -> UniqSet Core.Name -> Constraint
  deriving Eq

instance Ord Constraint where
  DomDom x y d <= DomDom x' y' d' = (x, y, d) <= (x', y', d')
  ConDom k x d <= ConDom k' x' d' = (k, x, d) <= (k', x', d')
  DomSet x d k <= DomSet x' d' k' = (x, d, nonDetEltsUniqSet k) <= (x', d', nonDetEltsUniqSet k')

  DomDom _ _ _ <= _            = True
  ConDom _ _ _ <= DomSet _ _ _ = True
  _            <= _            = False

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

-- Atomic constraints behave like an ordered pair of constructor sets
lhs :: Constraint -> K
lhs (DomDom x _ d) = Dom x d
lhs (ConDom k _ _) = Set (unitUniqSet k)
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
toAtomic (Set ks) (Dom x d) = fmap (\k -> ConDom k x d) $ nonDetEltsUniqSet ks
toAtomic (Set ks) (Set ks')
  | uniqSetAll (`elementOfUniqSet` ks') ks
              = []
  | otherwise = Core.pprPanic "Invalid subtyping constraint!" (Core.ppr (ks, ks'))

-- Is the first constraint stronger than the second?
entailsConstraint :: Constraint -> Constraint -> Bool
entailsConstraint c1 c2 = (lhs c1 `subset` lhs c2) && (rhs c2 `subset` rhs c1)






-- A guard is a conjunction of k in dom(X(d), grouped by X
newtype Guard = Guard (M.Map Int (S.Set (Core.Name, Core.Name)))
  deriving (Eq, Ord)

instance Refined Guard where
  domain (Guard m)     = M.keys m
  rename x y (Guard m) = Guard $ M.mapKeys (\x' -> if x == x' then y else x') m

instance Outputable Guard where
  ppr (Guard g) = sep (punctuate and [ppr k <+> char '∈' <+> ppr (Dom x d) | (x, kds) <- M.toList g, (k, d) <- S.toList kds])
    where
      elem = unicodeSyntax (char '∈') (docToSDoc $ Pretty.text "in")
      and  = unicodeSyntax (char '∧') (docToSDoc $ Pretty.text "&&")

-- Trivially true guard
top :: Guard
top = Guard M.empty

-- Guard generator
guardDom :: Core.Name -> Int -> Core.Name -> Guard
guardDom k x d = Guard $ M.singleton x (S.singleton (k ,d))

-- Conjunction of guards
and :: Guard -> Guard -> Guard
and (Guard m) (Guard m') = Guard $ M.unionWith S.union m m'

-- Remove a conjunction from a guard
delete :: Core.Name -> Int -> Core.Name -> Guard -> Guard
delete k x d (Guard m) = Guard $ M.adjust (S.delete (k, d)) x m

-- Replace a refinement variable y with x at a specific datatype d
replace :: Int -> Int -> Core.Name -> Guard -> Guard
replace x y d (Guard m) = Guard
                        $ M.insertWith S.union x preds                  -- Add preciates to x
                        $ M.adjust (S.filter (\(_, d') -> d /= d')) y m -- Remove predicates concerning d from y
  where
    preds =
      case M.lookup y m of
        Nothing -> S.empty
        Just s  -> S.filter (\(_, d') -> d == d') s

-- Is the first guard as strong as than the second?
entailsGuard :: Guard -> Guard -> Bool
entailsGuard (Guard m) (Guard m') = M.foldrWithKey (\x kds k -> k && pred x kds) True m'
  where
    pred x kds =
      case M.lookup x m of
        Just kds' -> S.isSubsetOf kds kds'
        Nothing   -> S.null kds

-- Insert a guard if it is not stronger than an existing guard, and remove guards which are stronger than it
insertGuard :: Guard -> S.Set Guard -> S.Set Guard
insertGuard g s
  | any (\g' -> entailsGuard g g') s = s                                 -- g is stronger than an existing guard
  | otherwise = S.insert g $ S.filter (\g' -> not (entailsGuard g' g)) s -- remove guards that are stronger than g


-- A collection of guarded constraints
newtype ConSet = ConSet (M.Map Constraint (S.Set Guard))
  deriving Eq

instance Refined ConSet where
   domain (ConSet m)     = concatMap domain (M.keys m) ++ concatMap domain (concatMap S.toList $ M.elems m)
   rename x y (ConSet m) = ConSet $ M.map (S.map (rename x y)) $ M.mapKeys (rename x y) m

instance Outputable ConSet where
  ppr cs = vcat [(if M.null m then Core.empty else ppr g <+> char '?') <+> ppr k1 <+> arrowt <+> ppr k2 | (k1, k2, g@(Guard m)) <- toList cs]


-- Empty set of constraints
empty :: ConSet
empty = ConSet M.empty

-- Combined constraint sets
union :: ConSet -> ConSet -> ConSet
union (ConSet cs) (ConSet cs') = ConSet $ M.unionWith (foldr insertGuard) cs cs'

-- Insert an atomic constraint, combining with existing guards
insertAtomic :: Constraint -> Guard -> ConSet -> ConSet
insertAtomic c g (ConSet cs) = ConSet $ M.insertWith (foldr insertGuard) c (S.singleton g) cs

-- Insert any constructor set constraint
insert :: K -> K -> Guard -> ConSet -> ConSet
insert k1 k2 g cs = foldr (`insertAtomic` g) cs (toAtomic k1 k2)

-- ConSet behaves like [(K, K, Guard)]
toList :: ConSet -> [(K, K, Guard)]
toList (ConSet m) = [(lhs c, rhs c, g) | (c, gs) <- M.toList m, g <- S.toList gs]

-- Add a guard to an entire set
guardWith :: Core.Name -> Int -> Core.Name -> ConSet -> ConSet
guardWith k x d (ConSet cs) = ConSet $ M.map (insertGuard (guardDom k x d)) cs

-- Guard a constraint set by one of the guards
-- guardAlts :: [Guard] -> ConSet -> ConSet
-- guardAlts gs (ConSet cs) = M.foldrWithKey (\c gs' cs -> foldr (\g cs gs') empty cs

-- Filter a constraint set to a certain domain
restrict :: [Int] -> ConSet -> ConSet
restrict xs (ConSet m) = ConSet
                       $ M.map (S.filter (all (`elem` xs) . domain))            -- Filter guards
                       $ M.filterWithKey (\c _ -> all (`elem` xs) $ domain c) m -- Filter copnstraints







-- Close a constrain set under the resolution rules
saturate :: [Int] -> ConSet -> ConSet
saturate xs = restrict xs . resolve
  where
    resolve cs
     | cross xs cs == cs = cs
     | otherwise         = resolve (cross xs cs)

-- Apply the function to every constraint and union the results
bind :: ConSet -> (Constraint -> Guard -> ConSet) -> ConSet
bind (ConSet m) f = M.foldrWithKey (\c gs cs -> foldr (\g -> union (f c g)) cs gs) empty m

-- Apply the resolution rules once
cross :: [Int] -> ConSet -> ConSet
cross xs cs = cs `bind` (\c g -> cs `bind` (\c' g' -> insertAtomic c  g  $
                                                      insertAtomic c' g' $
                                                      subs  c' g' c  g   $
                                                      weak  c' g' c  g   $
                                                      trans c' g' c  g   ))
  where
    --TODO: Only apply if both sides are relevant

    -- Transitive closure
    trans :: Constraint -> Guard -> Constraint -> Guard -> ConSet
    trans c g c' g'
      | rhs c == lhs c' = insert (lhs c) (rhs c') (g `and` g') empty
    trans _ _ _ _       = empty

    -- Weakening rule
    weak :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    weak c@(ConDom k x d) g c' g'@(Guard m) cs = insertAtomic c' (g `and` delete k x d g') cs
    weak _ _ _ _                            cs = cs

    -- Substitution rule
    subs :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    subs c@(DomDom x y d) g c' g'@(Guard m) cs = insertAtomic c' (g `and` replace x y d g') cs
    subs _ _ _ _                            cs = cs

