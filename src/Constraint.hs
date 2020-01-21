{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Constraint (
  K(..),
  con,
  set,

  Guard,
  guardDom,
  top,

  ConSet,
  empty,
  insert,
  union,
  guardWith,
  guardAlts,
  saturate,
) where

import Prelude hiding ((<>), and)

import Control.Monad

import UniqSet
import Data.Maybe
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import qualified Data.Set as SS
import qualified Data.Set.NonEmpty as S

import SrcLoc
import Outputable hiding (empty, isEmpty)
import qualified Pretty as Pretty
import qualified GhcPlugins as Core

import Types

-- General constructors set
data K where
  Dom :: Int -> Core.Name -> K
  Set :: UniqSet Core.Name -> Maybe RealSrcSpan -> K

instance Eq K where
  Dom x d == Dom x' d' = x == x' && d == d'
  Set s _ == Set s' _  = s == s'
  _       == _         = False

instance Refined K where
  domain (Dom x _) = [x]
  domain (Set _ _) = []

  rename x y (Dom x' d)
    | x == x'  = Dom y d
  rename _ _ c = c

instance Outputable K where
  ppr (Dom x d)         = text "dom" <> parens (ppr x <> parens (ppr d))
  ppr (Set ks _)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (docToSDoc $ Pretty.text "{}")
    | otherwise         = pprWithBars ppr (nonDetEltsUniqSet ks)

-- Convenient smart constructors
con :: Core.Name -> Maybe RealSrcSpan -> K
con n l = Set (unitUniqSet n) l

set :: [Core.Name] -> Maybe RealSrcSpan -> K
set s l = Set (mkUniqSet s) l

-- Origin of the constructor set in src
loc :: K -> Maybe RealSrcSpan
loc (Set _ l) = l
loc _         = Nothing

-- Is the first constructor set a susbet of the second
subset :: K -> K -> Bool
subset (Dom x d) (Dom x' d')  = x == x' && d == d'
subset (Set ks _) (Set ks' _) = uniqSetAll (`elementOfUniqSet` ks') ks
subset _ _                    = False






-- Internal (atomic) constraint
data Constraint where
  DomDom   :: Int -> Int -> Core.Name -> Constraint
  ConDom   :: Core.Name -> Int -> Core.Name -> Maybe RealSrcSpan -> Constraint
  DomSet   :: Int -> Core.Name -> UniqSet Core.Name -> Maybe RealSrcSpan -> Constraint

instance Eq Constraint where
  DomDom x y d   == DomDom x' y' d'   = (x, y, d) == (x', y', d')
  ConDom k x d _ == ConDom k' x' d' _ = (k, x, d) == (k', x', d')
  DomSet x d k _ == DomSet x' d' k' _ = (x, d, nonDetEltsUniqSet k) == (x', d', nonDetEltsUniqSet k')
  _              == _                 = False

instance Ord Constraint where
  DomDom x y d <= DomDom x' y' d'     = (x, y, d) <= (x', y', d')
  ConDom k x d _ <= ConDom k' x' d' _ = (k, x, d) <= (k', x', d')
  DomSet x d k _ <= DomSet x' d' k' _ = (x, d, nonDetEltsUniqSet k) <= (x', d', nonDetEltsUniqSet k')

  DomDom _ _ _   <= _              = True
  ConDom _ _ _ _ <= DomSet _ _ _ _ = True
  _              <= _              = False

instance Refined Constraint where
  domain (DomDom x y _ )  = [x, y] -- We assume x/=y
  domain (ConDom _ x _ _) = [x]
  domain (DomSet x _ _ _) = [x]

  rename x y (DomDom x' x'' d)
    | x == x'  = DomDom y x'' d
    | x == x'' = DomDom x' y d
  rename x y (ConDom k x' d l)
    | x == x' = ConDom k y d l
  rename x y (DomSet x' d ks r)
    | x == x' = DomSet y d ks r
  rename _ _ c = c

instance Outputable Constraint where
  ppr c = ppr (lhs c) <+> arrowt <+> ppr (rhs c)

-- Atomic constraints behave like a set of ordered pairs of constructor sets
lhs :: Constraint -> K
lhs (DomDom x _ d)   = Dom x d
lhs (ConDom k _ _ l) = Set (unitUniqSet k) l
lhs (DomSet x d _ r) = Dom x d

rhs :: Constraint -> K
rhs (DomDom _ y d)   = Dom y d
rhs (ConDom _ x d _) = Dom x d
rhs (DomSet _ _ k r) = Set k r

toAtomic :: K -> K -> Maybe [Constraint]
toAtomic (Dom x d) (Dom y d')
  | d /= d'   = Core.pprPanic "Invalid subtyping constraint!" (Core.ppr (d, d'))
  | x == y    = Just []
  | otherwise = Just [DomDom x y d]
toAtomic (Dom x d) (Set k l)  = Just [DomSet x d k l]
toAtomic (Set ks l) (Dom x d) = Just $ fmap (\k -> ConDom k x d l) $ nonDetEltsUniqSet ks
toAtomic (Set ks l) (Set ks' r)
  | uniqSetAll (`elementOfUniqSet` ks') ks
              = Just []
  | otherwise = Nothing

-- Is the first constraint stronger than the second?
entailsConstraint :: Constraint -> Constraint -> Bool
entailsConstraint c1 c2 = (lhs c1 `subset` lhs c2) && (rhs c2 `subset` rhs c1)






-- A guard is a conjunction of k in dom(X(d), grouped by (X, d)
newtype Guard = Guard (M.Map (Int, Core.Name) Core.Name)
  deriving (Eq, Ord)

instance Refined Guard where
  domain (Guard m)     = map fst $ M.keys m
  rename x y (Guard m) = Guard $ M.mapKeys (\(x', d) -> if x == x' then (y, d) else (x', d)) m

instance Outputable Guard where
  ppr (Guard g) = sep (punctuate and [ppr k <+> char '∈' <+> text "dom" <> parens (ppr x <> parens (ppr d)) | ((x, d), k) <- M.toList g])
    where
      elem = unicodeSyntax (char '∈') (docToSDoc $ Pretty.text "in")
      and  = unicodeSyntax (char '∧') (docToSDoc $ Pretty.text "&&")

-- Trivially true guard
top :: Guard
top = Guard M.empty

-- Guard generator
guardDom :: Core.Name -> Int -> Core.Name -> Guard
guardDom k x d = Guard $ M.singleton (x, d) k

-- Conjunction of guards
and :: Guard -> Guard -> Maybe Guard
and (Guard m) g = M.foldrWithKey go (Just g) m
  where
    go (x, d) k g = do
      Guard m <- g
      case M.lookup (x, d) m of
        Nothing -> return $ Guard $ M.insert (x, d) k m
        Just k' -> do
          guard (k == k')
          g

-- Remove a conjunction from a guard
delete :: Core.Name -> Int -> Core.Name -> Guard -> Guard
delete k x d (Guard m) = Guard $ M.update (\k' -> guard (k /= k') >> return k') (x, d) m

-- Replace a refinement variable y with x at a specific datatype d
replace :: Int -> Int -> Core.Name -> Guard -> Guard
replace x y d (Guard m) = Guard
                        $ M.update pred (x, d) -- Add preciate to x
                        $ M.delete (y, d) m    -- Remove predicate from y
  where
    pred k =
      case M.lookup (y, d) m of
        Nothing -> return k
        Just k' -> guard (k == k') >> return k

-- Is the first guard as strong as than the second?
entailsGuard :: Guard -> Guard -> Bool
entailsGuard (Guard m) (Guard m') = M.foldrWithKey (\x kds k -> k && pred x kds) True m'
  where
    pred x k =
      case M.lookup x m of
        Just k' -> k == k'
        Nothing -> False

-- Insert a guard if it is not stronger than an existing guard, and remove guards which are stronger than it
insertGuard :: Guard -> S.NESet Guard -> S.NESet Guard
-- insertGuard g s | Core.pprTrace "insertGuard" (Core.ppr (g, s)) False = undefined
insertGuard g s
 | any (\g' -> entailsGuard g g') s = s                                    -- g is stronger than an existing guard
 | otherwise = S.insertSet g $ S.filter (\g' -> not (entailsGuard g' g)) s -- remove guards that are stronger than g






-- A collection of guarded constraints
newtype ConSet = ConSet (M.Map Constraint (S.NESet Guard))
  deriving Eq

instance Refined ConSet where
   domain (ConSet m)     = L.nub (concatMap domain (M.keys m)) `L.union` concatMap domain (concatMap (NE.toList . S.toList) $ M.elems m)
   rename x y (ConSet m) = ConSet $ M.map (S.map (rename x y)) $ M.mapKeys (rename x y) m

instance Outputable ConSet where
  ppr cs = vcat [(if M.null m then Core.empty else ppr g <+> char '?') <+> ppr k1 <+> arrowt <+> ppr k2 | (k1, k2, g@(Guard m)) <- toList cs]

-- Empty set of constraints
empty :: ConSet
empty = ConSet M.empty

-- Is the constraint set empty
isEmpty :: ConSet -> Bool
isEmpty (ConSet m) = M.null m

-- Combined constraint sets
union :: ConSet -> ConSet -> ConSet
union (ConSet cs) (ConSet cs') = ConSet $ M.unionWith (foldr insertGuard) cs cs'

-- Insert an atomic constraint, combining with existing guards
insertAtomic :: Constraint -> Guard -> ConSet -> ConSet
-- insertAtomic _ g _ | Core.pprTrace "insertGuard" (Core.ppr g) False = undefined
insertAtomic c g (ConSet cs) = ConSet $ M.insertWith (foldr insertGuard) c (S.singleton g) cs

-- Insert any constructor set constraint
insert :: K -> K -> Guard -> ConSet -> ConSet
insert k1 k2 g cs =
  case toAtomic k1 k2 of
    Just cs' -> foldr (\c -> insertAtomic c g) cs cs'
    Nothing  -> Core.pprPanic "The program is unsound!" (Core.ppr (loc k1, loc k2))

-- ConSet behaves like [(K, K, Guard)]
toList :: ConSet -> [(K, K, Guard)]
toList (ConSet m) = [(lhs c, rhs c, g) | (c, gs) <- M.toList m, g <- NE.toList $ S.toList gs]

-- Surely there is a better way of doing this??
mapMaybeSet :: Ord b => (a -> Maybe b) -> S.NESet a -> Maybe (S.NESet b)
mapMaybeSet f = S.nonEmptySet . SS.fromList . mapMaybe f . SS.toList . S.toSet

-- Add a guard to an entire set
guardWith :: Core.Name -> Int -> Core.Name -> ConSet -> ConSet
guardWith k x d (ConSet cs) = ConSet $ M.mapMaybe (mapMaybeSet (and $ guardDom k x d)) cs

-- Guard a constraint set by one of the guards
guardAlts :: [Guard] -> ConSet -> ConSet
guardAlts gs (ConSet cs) =
  case S.nonEmptySet $ SS.fromList gs of
    Nothing  -> empty
    Just gs' -> ConSet $ M.mapMaybe (mapMaybeSet (uncurry and) . S.cartesianProduct gs') cs

-- Difference between to ConSets
diff :: ConSet -> ConSet -> ConSet
diff (ConSet m) (ConSet m') = ConSet $ M.mapMaybeWithKey go m
  where
    go c gs =
      case M.lookup c m' of
        Just gs' -> S.nonEmptySet (gs S.\\ gs')
        Nothing  -> Just gs

-- Filter a constraint set to a certain domain
restrict :: [Int] -> ConSet -> ConSet
restrict xs (ConSet m) = ConSet
                       $ M.mapMaybe (S.nonEmptySet . S.filter (all (`elem` xs) . domain))            -- Filter guards
                       $ M.filterWithKey (\c _ -> all (`elem` xs) $ domain c) m -- Filter constraints

-- Filter a constraint set to remove a variable
filterOut :: Int -> ConSet -> ConSet
filterOut x (ConSet m) = ConSet
                       $ M.mapMaybe (S.nonEmptySet . S.filter (notElem x . domain))            -- Filter guards
                       $ M.filterWithKey (\c _ -> x `notElem` domain c) m -- Filter constraints

-- Filter a constraint set to one which reference a variable
filterTo :: Int -> ConSet -> ConSet
filterTo x (ConSet m) = ConSet
                      $ M.mapMaybeWithKey (\c gs -> if x `elem` domain c then Just gs else S.nonEmptySet $ S.filter (elem x . domain) gs) m -- Filter guards







-- Close a constrain set under the resolution rules
saturate :: [Int] -> ConSet -> ConSet
saturate xs cs = foldr (\x cs' -> filterOut x $ saturate' x cs' $ filterTo x cs') cs inter
  where
    inter = domain cs L.\\ xs

    saturate' :: Int -> ConSet -> ConSet -> ConSet
    -- saturate' x _ cs | Core.pprTrace "todo" (Core.ppr (x, cs)) False = undefined
    saturate' x done cs@(ConSet todo)
      | isEmpty cs = done
      | otherwise  = saturate' x new (filterTo x $ diff new done)
      where
        new = M.foldrWithKey (\c gs -> cross c gs) done todo

-- Apply the resolution rules once between the new constraint and the old
cross :: Constraint -> S.NESet Guard -> ConSet -> ConSet
cross c gs cs@(ConSet m) =
  M.foldrWithKey (\c' gs' cs' ->
    S.foldr (\(g, g') ->
      subs c' g' c g  .
      subs c g c' g'  .
      weak c' g' c g  .
      weak c g c' g'  .
      trans c g c' g' .
      trans c' g' c g
    ) cs' $ S.cartesianProduct gs gs'
  ) cs m

  where
    -- Transitive closure
    trans :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    trans c g c' g'
      | rhs c == lhs c'
      , Just g'' <- g `and` g' = insert (lhs c) (rhs c') g''
    trans _ _ _ _              = id

    -- Weakening rule
    weak :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    weak c@(ConDom k x d l) g c' g'@(Guard m)
      | Just g'' <- g `and` delete k x d g' = insertAtomic c' g''
    weak _ _ _ _                            = id

    -- Substitution rule
    subs :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    subs c@(DomDom x y d) g c' g'@(Guard m)
      | Just g'' <- g `and` replace x y d g' = insertAtomic c' g''
    subs _ _ _ _                             = id

