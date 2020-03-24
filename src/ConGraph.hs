module ConGraph (
  ConGraph,
  empty,
  guard,
  union,
  singleton,
  restrict,
) where

import Prelude hiding (lookup, (<>))
import Control.Monad hiding (guard)
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S

import Types
import Guard

import Name
import Binary
import UniqSet
import Outputable hiding (empty, isEmpty)

-- Nested map utilities
-- Lookup guard between two notes
lookup :: K -> K -> M.Map K (M.Map K GuardSet) -> GuardSet
lookup x y m = fromMaybe bot (M.lookup x m >>= M.lookup y)

lookupToX :: K -> Int -> M.Map K (M.Map K GuardSet) -> GuardSet
lookupToX x y m = fromMaybe bot (M.lookup x m >>= lookupX y)

lookupFromX :: Int -> K -> M.Map K (M.Map K GuardSet) -> GuardSet
lookupFromX x y m = fromMaybe bot (lookupX x m >>= M.lookup y)

lookupX :: Int -> M.Map K a -> Maybe a
lookupX x m =
  case [ a | (Dom y _, a) <- M.toList m, x == y ] of
    []    -> Nothing
    (a:_) -> Just a -- Nodes must have a unique datatype

instance (Refined k, Ord k, Refined a) => Refined (M.Map k a) where
  domain m =
    let keydom = foldr (S.union . domain) S.empty $ M.keysSet m
    in  foldr (S.union . domain) keydom m
  rename x y = M.mapKeys (rename x y) . M.map (rename x y)






-- A collection of disjoint graphs for each datatype
-- Nodes are constructor sets or refinement variables
-- Edges are labelled by possible guards.
newtype ConGraph = ConGraph (M.Map Name (M.Map K (M.Map K GuardSet)))

instance Refined ConGraph where
  domain (ConGraph cg)    = foldr (S.union . domain) S.empty cg
  rename x y (ConGraph m) = ConGraph $ M.map (rename x y) m

instance Outputable ConGraph where
  ppr (ConGraph cg) = vcat [ ppr g <+> ppr k1 <+> arrowt <+> ppr k2
                             | (_, m) <- M.toList cg,
                               (k1, m') <- M.toList m,
                               (k2, gs) <- M.toList m',
                               g <- toList gs]

instance Binary ConGraph where
  put_ bh (ConGraph cg) = put_ bh [ (n, [ (k1, M.toList m') | (k1, m') <- M.toList m]) | (n, m) <- M.toList cg]
  get bh = do
    nl <- get bh
    let nl' = [(n, M.fromList [(k, M.fromList m') | (k, m') <- l]) | (n, l) <- nl :: [(Name, [(K, [(K, GuardSet)])])]]
    return (ConGraph $ M.fromList nl')

-- An empty set
empty :: ConGraph
empty = ConGraph M.empty

-- A new (non-atomic) constraint with trivial guard
singleton :: K -> K -> Maybe ConGraph
singleton (Dom x d) (Dom y d')
  | d /= d'   = pprPanic "Constraint between types of different shape!" $ ppr (d, d')
  | x == y    = Just empty
  | otherwise = Just $ ConGraph $ M.singleton d $ M.singleton (Dom x d) $ M.singleton (Dom y d) top
singleton (Dom x d) (Set k l)
              = Just $ ConGraph $ M.singleton d $ M.singleton (Dom x d) $ M.singleton (Set k l) top
singleton (Set ks l) (Dom x d)
              = Just $ ConGraph $ M.singleton d $ M.fromList [ (con k l, M.singleton (Dom x d) top) | k <- nonDetEltsUniqSet ks]
singleton k1 k2
  | safe k1 k2 = Just empty
  | otherwise  = Nothing

-- Guard a constraint graph by a set of possible guards
guard :: S.Set Name -> Int -> Name -> ConGraph -> ConGraph
guard ks x d (ConGraph cg) = ConGraph $ M.map (M.map (M.map (dom ks x d &&&))) cg

-- Combine two constraint graphs
union :: ConGraph -> ConGraph -> ConGraph
union (ConGraph x) (ConGraph y) = ConGraph $ M.unionWith (M.unionWith (M.unionWith (|||))) x y

-- Restrict a constraint graph to it's interface and check satisfiability
restrict :: S.Set Int -> ConGraph -> Either (K, K) ConGraph
restrict interface cg = {- min . sat -} trans inner cg >>= weaken inner
  where
    inner = domain cg S.\\ interface

-- Take the transitive closure of a graph over an internal set
trans :: S.Set Int -> ConGraph -> Either (K, K) ConGraph
trans xs (ConGraph g) = ConGraph <$> sequence (M.map (\m -> foldM transX m xs) g)

-- Add transitive connections that pass through node x
transX :: M.Map K (M.Map K GuardSet) -> Int -> Either (K, K) (M.Map K (M.Map K GuardSet))
transX m x = sequence $ M.fromSet (\i -> sequence $ M.fromSet (go i) to) from
  where
    from = M.keysSet m
    to   = M.foldr (S.union . M.keysSet) S.empty m
    go i j
      | i == j = Right bot
      | otherwise =
        let new_guard = lookup i j m ||| (lookupToX i x m &&& lookupFromX x j m)
        in if safe i j || isEmpty new_guard
          then Right new_guard
          else Left (i, j)

-- Weaken every occurs of intermediate notes in the guards
weaken :: S.Set Int -> ConGraph -> Either (K, K) ConGraph
weaken xs cg = foldM weakenX cg xs
  where
    weakenX :: ConGraph -> Int -> Either (K, K) ConGraph
    weakenX (ConGraph g) x =
      let preds = M.foldr (\m -> M.unionWith (|||) $ M.mapMaybe (lookupX x) $ M.filterWithKey (\k _ -> nonX k m) m) M.empty g
      in ConGraph <$> sequence (M.mapWithKey (subPreds preds x) g)

    --- Don't weaken to another intermediate node
    nonX :: K -> M.Map K (M.Map K GuardSet) -> Bool
    nonX k@(Dom x _) m = (x `notElem` xs) && M.null (M.mapMaybe (M.lookup k) m)
    nonX k           m = M.null (M.mapMaybe (M.lookup k) m)

-- Apply a pred map to an individual graph and remove that intermediate node
subPreds :: M.Map K GuardSet -> Int -> Name -> M.Map K (M.Map K GuardSet) -> Either (K, K) (M.Map K (M.Map K GuardSet))
subPreds preds x d =
  sequence . M.mapMaybeWithKey (\i ->
    if i == Dom x d
      then const Nothing
      else Just . sequence . M.mapMaybeWithKey (\j gs ->
        if j == Dom x d
          then Nothing
          else let new_guard = M.foldrWithKey alt gs preds
            in if safe i j || isEmpty new_guard
              then Just $ Right new_guard
              else Just $ Left (i, j)))
  where
    alt :: K -> GuardSet -> GuardSet -> GuardSet
    alt n g g' = g' ||| replace x d n g' &&& g

-- Remove intermediate nodes and guards
-- DEPRECIATED
purge :: S.Set Int -> ConGraph -> ConGraph
purge xs (ConGraph g) = ConGraph $ M.map (M.mapMaybeWithKey (mapI (M.mapMaybeWithKey (mapI $ filterGuards xs)))) g
  where
    -- Apply the function if K is not being removed
    mapI :: (a -> b) -> K -> a -> Maybe b
    mapI _ (Dom x _) _
      | x `elem` xs = Nothing
    mapI f _ a      = Just (f a)
