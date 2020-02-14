{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Constraint (
  SrcSpan(..),
  K(..),
  con,
  set,

  Guard,

  ConSet,
  toList,
  fromList,
  empty,
  insert,
  union,
  guardWith,
  guardAlts,
  saturate,
) where

import Prelude hiding ((<>), and)

import UniqSet
import Unique
import Data.Hashable
import qualified Data.List as L
import qualified Data.List.NonEmpty as NE
import qualified Data.HashMap.Lazy as H
import qualified Data.Set as SS
import qualified Data.Set.NonEmpty as S

import SrcLoc
import Outputable hiding (empty, isEmpty)
import qualified Pretty
import qualified GhcPlugins as Core

import Types

-- General constructors set
data K where
  Dom :: Int -> Core.Name -> K
  Set :: UniqSet Core.Name -> SrcSpan -> K

instance Eq K where
  Dom x d == Dom x' d' = x == x' && d == d'
  Set s _ == Set s' _  = s == s'
  _       == _         = False

instance Hashable Core.Unique where
  hashWithSalt s u = hashWithSalt s (Unique.getKey u)

instance Hashable K where
  hashWithSalt s (Dom x d)  = hashWithSalt s (x, Unique.getUnique d)
  hashWithSalt s (Set ks _) = hashWithSalt s (nonDetKeysUniqSet ks)

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
con :: Core.Name -> SrcSpan -> K
con n = Set (unitUniqSet n)

set :: [Core.Name] -> SrcSpan -> K
set s = Set (mkUniqSet s)

-- Origin of the constructor set in src
tag :: K -> SrcSpan
tag (Set _ l) = l
tag _         = UnhelpfulSpan (Core.mkFastString "Unkown origin!")

-- Possible heuristic for Ord?
-- size :: K -> Maybe Int
-- size (Dom _ _) = Nothing
-- size (Set l _) = Just $ sizeUniqSet l

-- Is the first constructor set a susbet of the second
-- subset :: K -> K -> Bool
-- subset (Dom x d) (Dom x' d')  = x == x' && d == d'
-- subset (Set ks _) (Set ks' _) = uniqSetAll (`elementOfUniqSet` ks') ks
-- subset _ _                    = False






-- Internal (atomic) constraint
data Constraint where
  DomDom   :: Int -> Int -> Core.Name -> Constraint
  ConDom   :: Core.Name -> Int -> Core.Name -> SrcSpan -> Constraint
  DomSet   :: Int -> Core.Name -> UniqSet Core.Name -> SrcSpan -> Constraint

instance Eq Constraint where
  DomDom x y d   == DomDom x' y' d'   = (x, y, d) == (x', y', d')
  ConDom k x d _ == ConDom k' x' d' _ = (k, x, d) == (k', x', d')
  DomSet x d k _ == DomSet x' d' k' _ = (x, d, nonDetEltsUniqSet k) == (x', d', nonDetEltsUniqSet k')
  _              == _                 = False

-- TODO: Include size heuristic in the ord
instance Ord Constraint where
  DomDom x y d   <= DomDom x' y' d'   = (x, y, d) <= (x', y', d')
  ConDom k x d _ <= ConDom k' x' d' _ = (k, x, d) <= (k', x', d')
  DomSet x d k _ <= DomSet x' d' k' _ = (x, d, nonDetEltsUniqSet k) <= (x', d', nonDetEltsUniqSet k')

  DomDom {} <= _         = True
  ConDom {} <= DomSet {} = True
  _         <= _         = False

instance Hashable Constraint where
  hashWithSalt s u = hashWithSalt s (lhs u, rhs u)

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
lhs (DomSet x d _ _) = Dom x d

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
toAtomic (Set ks l) (Dom x d) = Just ((\k -> ConDom k x d l) <$> nonDetEltsUniqSet ks)
toAtomic (Set ks _) (Set ks' _)
  | uniqSetAll (`elementOfUniqSet` ks') ks
              = Just []
  | otherwise = Nothing

-- Is the first constraint stronger than the second?
-- entailsConstraint :: Constraint -> Constraint -> Bool
-- entailsConstraint c1 c2 = (lhs c1 `subset` lhs c2) && (rhs c2 `subset` rhs c1)









-- A guard, i.e. a set of (X, k)
type Guard = SS.Set (Int, Core.Name)

instance Refined Guard where
  domain = SS.foldr (\(x, _) -> (x:)) []
  rename x y = SS.map (\(x', k) -> if x == x' then (y, k) else (x', k))

pprGuard :: Guard -> SDoc
pprGuard g = sep (punctuate and [ppr k <+> char '∈' <+> text "dom" <> parens (ppr x) | (x, k) <- SS.toList g])
  where
    elem = unicodeSyntax (char '∈') (docToSDoc $ Pretty.text "in")
    and  = unicodeSyntax (char '∧') (docToSDoc $ Pretty.text " &&")

-- Insert a guard if it is not stronger than an existing guard, and remove guards which are stronger than it
insertGuard :: Guard -> S.NESet Guard -> S.NESet Guard
insertGuard g s
 | any (`SS.isSubsetOf` g) s = s                                  -- g is stronger than an existing guard
 | otherwise = S.insertSet g $ S.filter (not . SS.isSubsetOf g) s -- remove guards that are stronger than g









-- A collection of guarded constraints
newtype ConSet = ConSet (H.HashMap Constraint (S.NESet Guard))
  deriving Eq

instance Refined ConSet where
   domain (ConSet m)     = L.nub (concatMap domain (H.keys m)) `L.union` concatMap domain (concatMap (NE.toList . S.toList) $ H.elems m)
   rename x y (ConSet m) = ConSet $ H.fromList $ fmap (\(k, v) -> (rename x y k, S.map (rename x y) v)) $ H.toList m

instance Outputable ConSet where
  ppr cs = vcat [(if SS.null g then Core.empty else pprGuard g <+> char '?') <+> ppr k1 <+> arrowt <+> ppr k2 | (k1, k2, g) <- toList cs]

-- Empty set of constraints
empty :: ConSet
empty = ConSet H.empty

-- Combined constraint sets
union :: ConSet -> ConSet -> ConSet
union (ConSet cs) (ConSet cs') = ConSet $ H.unionWith (foldr insertGuard) cs cs'

-- Insert an atomic constraint, combining with existing guards
insertAtomic :: Constraint -> Guard -> ConSet -> ConSet
insertAtomic c g (ConSet cs) = ConSet $ H.insertWith (foldr insertGuard) c (S.singleton g) cs

-- Insert any constructor set constraint
insert :: K -> K -> Guard -> Core.Expr Core.Var -> ConSet -> ConSet
insert k1 k2 g e cs =
  case toAtomic k1 k2 of
    Just cs' -> foldr (`insertAtomic` g) cs cs'
    Nothing  -> Core.pprPanic "The program is unsound!" (Core.ppr (k1, tag k1, k2, tag k2, g, e, cs))

-- ConSet behaves like [(K, K, Guard)]
toList :: ConSet -> [(K, K, Guard)]
toList (ConSet m) = [(lhs c, rhs c, g) | (c, gs) <- H.toList m, g <- NE.toList $ S.toList gs]

fromList :: [(K, K, Guard)] -> ConSet
fromList [] = empty
fromList ((k1, k2, g):cs) = insert k1 k2 g undefined (fromList cs)

-- Surely there is a better way of doing this??
-- mapMaybeSet :: Ord b => (a -> Maybe b) -> S.NESet a -> Maybe (S.NESet b)
-- mapMaybeSet f = S.nonEmptySet . SS.fromList . mapMaybe f . SS.toList . S.toSet

-- Add a guard to an entire set
guardWith :: Int -> Core.Name -> ConSet -> ConSet
guardWith x k (ConSet cs) = ConSet $ H.map (S.map (SS.union $ SS.singleton (x, k))) cs

-- Guard a constraint set by one of the guards
guardAlts :: [Guard] -> ConSet -> ConSet
guardAlts gs (ConSet cs) =
  case S.nonEmptySet $ SS.fromList gs of
    Nothing  -> empty
    Just gs' -> ConSet $ H.map (S.map (uncurry SS.union) . S.cartesianProduct gs') cs

-- Difference between to Constraint sets
diff :: ConSet -> ConSet -> ConSet
diff (ConSet m) (ConSet m') = ConSet $ H.mapMaybeWithKey go m
  where
    go c gs =
      case H.lookup c m' of
        Just gs' -> S.nonEmptySet (gs S.\\ gs')
        Nothing  -> Just gs

-- Filter guards in a coarse or fine mode
-- notEmpty :: (Guard -> Bool) -> H.HashMap Constraint (S.NESet Guard) -> ConSet
-- notEmpty f hm = ConSet $ H.map go hm'
--   where
--     hm' = H.map (S.filter f) hm
--     go s =
--       case S.nonEmptySet s of
--         Nothing -> S.insertSet SS.empty s -- Trivially true guard
--         Just s' -> s'

-- Filter a constraint set to remove a variable
filterOut :: Int -> ConSet -> ConSet
filterOut x (ConSet m) = ConSet
                       $ H.mapMaybe (S.nonEmptySet . S.filter (notElem x . domain)) -- Filter guards
                       $ H.filterWithKey (\c _ -> x `notElem` domain c) m           -- Filter constraints

-- Filter a constraint set to one which reference a variable
filterTo :: Int -> ConSet -> ConSet
filterTo x (ConSet m) = ConSet
                      $ H.mapMaybeWithKey (\c gs -> if x `elem` domain c then Just gs else S.nonEmptySet $ S.filter (elem x . domain) gs) m -- Filter guards







-- Close a constrain set under the resolution rules
saturate :: Core.Expr Core.Var -> [Int] -> ConSet -> ConSet
saturate e xs cs = foldr (\x cs' -> filterOut x $ saturate' x cs' $ filterTo x cs') cs inter
  where
    inter = domain cs L.\\ xs

    saturate' :: Int -> ConSet -> ConSet -> ConSet
    saturate' x done (ConSet todo)
      | H.null todo = done
      | otherwise   = saturate' x new (filterTo x $ diff new done)
      where
        new = H.foldrWithKey (cross x e) done todo

-- Apply the resolution rules once between the new constraint and the old
cross :: Int -> Core.Expr Core.Var -> Constraint -> S.NESet Guard -> ConSet -> ConSet
cross z e c gs cs@(ConSet m) =

   H.foldrWithKey (\c' gs' cs' ->
    S.foldr (\(g, g') ->
       trans c g c' g' .
       trans c' g' c g .
       subs c' g' c g  .
       subs c g c' g'  .
       weak c' g' c g  .
       weak c g c' g'
     ) cs' $ S.cartesianProduct gs gs'
   ) cs m

  where
    -- Transitive closure
    trans :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    trans c g c' g'
      | rhs c == lhs c'
      , z `elem` (domain c ++ domain c') = insert (lhs c) (rhs c') (g `SS.union` g') e
    trans _ _ _ _              = id

    -- Weakening rule
    weak :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    weak (ConDom k x _ _) g c' g'
      | x == z = insertAtomic c' (g `SS.union` SS.delete (x, k) g')
    weak _ _ _ _                            = id

    -- Substitution rule
    subs :: Constraint -> Guard -> Constraint -> Guard -> (ConSet -> ConSet)
    subs (DomDom x y _) g c' g'
      | y == z = insertAtomic c' (g `SS.union` rename y x g')
    subs _ _ _ _                             = id

