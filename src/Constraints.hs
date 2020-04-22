{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Constraints
  ( Side (..),
    K (..),
    safe,
    toAtomic,
    Guard (..),
    GuardSet (..),
    toList,
    isEmpty,
    dom,
    applyPreds,
  )
where

--     (&&&),
--     (|||),
--     toList,
--     top,
--     bot,
--     minimise,
--     bind,
--     dom,
--     isEmpty,
--     applyPreds,

import Binary
import Control.Monad
import Data.Hashable
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import Name
import Outputable hiding (isEmpty)
import SrcLoc hiding (L)
import Types
import UniqSet
import Unique
import Prelude hiding ((<>), and, map)

-- Atomic constructors set
data Side = L | R

data K (s :: Side) where
  Dom :: Int -> K s
  Set :: UniqSet Name -> SrcSpan -> K R
  Con :: Name -> SrcSpan -> K L

-- Disregard srcspan in comparison
instance Eq (K s) where
  Dom x == Dom x' = x == x'
  Set s _ == Set s' _ = s == s'
  Con k _ == Con k' _ = k == k'
  _ == _ = False

instance Ord (K s) where
  Dom x <= Dom x' = x <= x'
  Set k _ <= Set k' _ = nonDetEltsUniqSet k <= nonDetEltsUniqSet k'
  Con k _ <= Con k' _ = k <= k'
  Dom _ <= _ = True
  _ <= _ = False

instance Refined (K s) where
  freevs (Dom x) = [x]
  freevs (Con _ _) = []
  freevs (Set _ _) = []

  rename x y (Dom x')
    | x == x' = Dom y
  rename _ _ c = c

instance Outputable (K s) where
  ppr (Dom x) = text "dom" <> parens (ppr x)
  ppr (Con k _) = ppr k
  ppr (Set ks _)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (ppr "{}")
    | otherwise = pprWithBars ppr (nonDetEltsUniqSet ks)

instance Binary (K L) where
  put_ bh (Dom x) = put_ bh True >> put_ bh x
  put_ bh (Con k l) = put_ bh False >> put_ bh k >> put_ bh l

  get bh = do
    n <- get bh
    if n
      then do
        x <- get bh
        return (Dom x)
      else do
        k <- get bh
        l <- get bh
        return (Con k l)

instance Binary (K R) where
  put_ bh (Dom x) = put_ bh True >> put_ bh x
  put_ bh (Set s l) = put_ bh False >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh = do
    n <- get bh
    if n
      then Dom <$> get bh
      else Set . mkUniqSet <$> get bh <*> get bh

instance Hashable (K s) where
  hashWithSalt s (Dom x) = hashWithSalt s x
  hashWithSalt s (Set ks _) = hashWithSalt s (getKey <$> nonDetKeysUniqSet ks)
  hashWithSalt s (Con k _) = hashWithSalt s (getKey $ getUnique k)

-- Is a pair of constructor sets safe
safe :: K l -> K r -> Bool
safe (Set ks _) (Set ks' _) = uniqSetAll (`elementOfUniqSet` ks') ks
safe (Con k _) (Set ks _) = elementOfUniqSet k ks
safe (Set ks _) (Con k _) = nonDetEltsUniqSet ks == [k]
safe _ _ = True

-- Convert constraint to atomic form
toAtomic :: K l -> K r -> Maybe [(K L, K R)]
toAtomic (Dom x) (Dom y)
  | x /= y = Just [(Dom x, Dom y)]
toAtomic (Dom x) (Set k l) =
  Just [(Dom x, Set k l)]
toAtomic (Set ks l) (Dom x) =
  Just [(Con k l, Dom x) | k <- nonDetEltsUniqSet ks]
toAtomic (Con k l) (Dom x) =
  Just [(Con k l, Dom x)]
toAtomic k1 k2
  | safe k1 k2 = Just []
  | otherwise = Nothing

-- A guard, i.e. a set of constraints of the form k in (X, d)
-- Grouped by d
newtype Guard = Guard (M.Map (DataType Name) (S.Set (Int, Name)))
  deriving (Eq, Ord)

instance Refined Guard where
  freevs (Guard g) = M.foldr (\c l -> foldr L.insert l $ fst <$> S.toList c) [] g
  rename x y (Guard g) = Guard $ fmap (S.map (\(x', k) -> if x == x' then (y, k) else (x', k))) g

instance Outputable Guard where
  ppr (Guard g)
    | all S.null g = empty
    | otherwise = sep (punctuate and [dom k x d | (d, xks) <- M.toList g, (x, k) <- S.toList xks]) <+> char '?'
    where
      dom k x d = ppr k <+> elem <+> text "dom" <> parens (ppr x <> parens (ppr d))
      elem = unicodeSyntax (char '∈') (text "in")
      and = unicodeSyntax (char '∧') (text " & ")

instance Binary Guard where
  put_ bh (Guard m) = put_ bh [(n, S.toList s) | (n, s) <- M.toList m]
  get bh = do
    l <- get bh
    return $ Guard $ M.fromList [(n, S.fromList l') | (n, l') <- l]

and :: Guard -> Guard -> Guard
and (Guard m) (Guard m') = Guard (M.unionWith S.union m m')

-- A collection of possible guards
infix 2 :||

infix 3 :&&

data GuardSet where
  Top :: GuardSet
  Bottom :: GuardSet
  Single :: Guard -> GuardSet
  (:||) :: GuardSet -> GuardSet -> GuardSet
  (:&&) :: GuardSet -> GuardSet -> GuardSet
  Min :: S.Set Guard -> GuardSet
  deriving (Eq, Ord)

map :: (Guard -> Guard) -> GuardSet -> GuardSet
map _ Top = Top
map _ Bottom = Bottom
map f (Min s) = Min $ S.map f s
map f (Single s) = Single $ f s
map f (g :|| g') = map f g :|| map f g'
map f (g :&& g') = map f g :&& map f g'

-- bind :: GuardSet -> (Guard -> GuardSet) -> GuardSet
-- bind Bottom _ = Bottom
-- bind (Single s) f = f s
-- bind (Alt gs) f = Alt $ S.map (`bind` f) gs
-- bind (And gs) f = And $ S.map (`bind` f) gs

instance Refined GuardSet where
  freevs (Min g) = S.foldr (L.union . freevs) [] g
  freevs Top = []
  freevs Bottom = []
  freevs (Single s) = freevs s
  freevs (g :|| g') = freevs g `L.union` freevs g'
  freevs (g :&& g') = freevs g `L.union` freevs g'

  rename x y = map (rename x y)

instance Binary GuardSet where
  put_ bh Top = put_ bh (0 :: Int)
  put_ bh Bottom = put_ bh (1 :: Int)
  put_ bh (Single g) = put_ bh (2 :: Int) *> put_ bh g
  put_ bh (g :|| g') = put_ bh (3 :: Int) *> put_ bh g *> put_ bh g'
  put_ bh (g :&& g') = put_ bh (4 :: Int) *> put_ bh g *> put_ bh g'

  get bh = do
    i <- get bh
    case i :: Int of
      0 -> return Top
      1 -> return Bottom
      2 -> Single <$> get bh
      3 -> (:||) <$> get bh <*> get bh
      4 -> (:&&) <$> get bh <*> get bh

instance Outputable GuardSet where
  ppr = ppr . toList

toList :: GuardSet -> [Guard]
toList Bottom = []
toList (Min g) = S.toList g
toList Top = [Guard M.empty]
toList (Single g) = [g]
toList (g :|| g') = toList g ++ toList g'
toList (g :&& g') = liftM2 and (toList g) (toList g')

-- Asserts that X contain an element from ks
dom :: [Name] -> Int -> DataType Name -> GuardSet
dom ks x d = foldr (\k -> (:||) $ Single $ Guard $ M.singleton d $ S.singleton (x, k)) Bottom ks

-- An unsatisfiable guard
isEmpty :: GuardSet -> Bool
isEmpty Top = False
isEmpty Bottom = True
isEmpty (Single s) = False
isEmpty (g :|| g') = isEmpty g && isEmpty g'
isEmpty (g :&& g') = isEmpty g || isEmpty g'
isEmpty (Min g) = all (\(Guard g) -> M.null g) g

--
-- -- Replace X(d) with k in a guard and reduce
-- replace :: Int -> DataType Name -> K L -> GuardSet -> GuardSet
-- replace x d k = map go
--   where
--     go :: Guard -> Guard
--     go (Guard g) =
--       case k of
--         Dom y -> Guard $ M.adjust (S.map (\(x', c) -> if x == x' then (y, c) else (x', c))) d g
--         Con c _ -> Guard $ M.adjust (S.filter (/= (x, c))) d g
--
-- -- Remove guards concerning the intermediate nodes
-- remove :: Int -> GuardSet -> GuardSet
-- remove x gs =
--   bind
--     gs
--     ( \g ->
--         if x `elem` freevs g
--           then Bottom
--           else Single g
--     )
--

minOr :: S.Set Guard -> S.Set Guard -> S.Set Guard
minOr = S.foldr minInsert

minAnd :: S.Set Guard -> S.Set Guard -> S.Set Guard
minAnd g g' = S.foldr (\(a, b) -> minInsert (a `and` b)) S.empty $ S.cartesianProduct g g'

minimise :: GuardSet -> S.Set Guard
minimise Top = S.singleton (Guard $ M.empty)
minimise Bottom = S.empty
minimise (Single g) = S.singleton g
minimise (g :|| g') = minimise g `minOr` minimise g'
minimise (g :&& g') = minimise g `minAnd` minimise g'

minInsert :: Guard -> S.Set Guard -> S.Set Guard
minInsert g gs
  | any (`weaker` g) gs = gs
  | otherwise = S.insert g $ S.filter (not . weaker g) gs

-- Determine if the first guard is smaller than the second
weaker :: Guard -> Guard -> Bool
weaker (Guard g) (Guard g') = M.null $ M.differenceWith go g g'
  where
    -- Check size as a possible short cut
    go l r =
      if S.size l > S.size r || any (`notElem` r) l
        then Just l
        else Nothing

-- Apply predecessor maps to a guardset, i.e. remove and replace
applyPreds :: M.Map (DataType Name) (M.Map Int (M.Map (K L) GuardSet)) -> GuardSet -> GuardSet
applyPreds preds g = Min $ applyPreds' (S.singleton (Guard M.empty)) preds g
  where
    applyPreds' :: S.Set Guard -> M.Map (DataType Name) (M.Map Int (M.Map (K L) GuardSet)) -> GuardSet -> S.Set Guard
    applyPreds' gk preds (Min gs) = S.foldr (minOr . applyPreds' gk preds . Single) S.empty gs
    applyPreds' gk _ Top = gk
    applyPreds' gk _ Bottom = S.empty
    applyPreds' gk preds (g :|| g') = applyPreds' gk preds g `minOr` applyPreds' gk preds g'
    applyPreds' gk preds (g :&& g') = applyPreds' (applyPreds' gk preds g) preds g'
    applyPreds' gk preds (Single (Guard g)) =
      M.foldrWithKey
        ( \d d_guards gk' ->
            case M.lookup d preds of
              Nothing -> S.singleton (Guard (M.singleton d d_guards)) `minAnd` gk'
              Just d_preds -> S.foldr (go d d_preds) gk' d_guards
        )
        gk
        g
    go :: DataType Name -> M.Map Int (M.Map (K 'L) GuardSet) -> (Int, Name) -> S.Set Guard -> S.Set Guard
    go d d_preds (x, k) gs = gs `minAnd`
      case M.lookup x d_preds of
        Nothing -> S.singleton (Guard (M.singleton d (S.singleton (x, k))))
        Just m ->
          M.foldrWithKey
              ( \p pg acc ->
                  case p of
                    Dom y -> minInsert (Guard $ M.singleton d (S.singleton (y, k))) acc
                    Con k' _
                      | k == k' -> minimise pg `minOr` acc
                      | otherwise -> minInsert (Guard $ M.singleton d (S.singleton (x, k))) acc
              )
              S.empty
              m
--S.foldr (\(x, k) acc'' -> go d (x, k) &&& acc'') acc' d_guards) Top g
--   where
--     go :: DataType Name -> (Int, Name) -> GuardSet
--     go d (x, k) =
--       case M.lookup d preds >>= M.lookup x of
--         Just xd_preds ->
--           M.foldrWithKey
--             ( \p pg acc ->
--                 case p of
--                   Dom y -> (dom [k] y d &&& pg) ||| acc
--                   Con k' _
--                     | k == k' -> pg ||| acc
--                     | otherwise -> dom [k] x d ||| acc
--             )
--             Bottom
--             xd_preds
--         Nothing -> Bottom -- If there are no predecessors to X(d), we can assume it is false.
