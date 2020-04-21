{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Constraints
  ( Side (..),
    K (..),
    safe,
    toAtomic,
    Guard,
    GuardSet,
    (&&&),
    (|||),
    toList,
    top,
    dom,
    isEmpty,
    minimise,
    applyPreds,
  )
where

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
data GuardSet where
  Bottom :: GuardSet
  Single :: Guard -> GuardSet
  Alt :: S.Set GuardSet -> GuardSet
  And :: S.Set GuardSet -> GuardSet
  deriving (Eq, Ord)

infix 2 |||

{-# INLINE (|||) #-}
Bottom ||| g = g
g ||| Bottom = g
Alt gs ||| Alt gs' = Alt (S.union gs gs')
Alt gs ||| g = Alt (S.insert g gs)
g ||| Alt gs = Alt (S.insert g gs)
g ||| g' = Alt (S.fromList [g, g'])

infix 3 &&&

{-# INLINE (&&&) #-}
Bottom &&& _ = Bottom
_ &&& Bottom = Bottom
And gs &&& And gs' = And (S.union gs gs')
And gs &&& g = And (S.insert g gs)
g &&& And gs = And (S.insert g gs)
g &&& g' = And (S.fromList [g, g'])

{-# INLINE map #-}
map :: (Guard -> Guard) -> GuardSet -> GuardSet
map _ Bottom = Bottom
map f (Single s) = Single $ f s
map f (Alt gs) = Alt $ S.map (map f) gs
map f (And gs) = And $ S.map (map f) gs

{-# INLINE bind #-}
bind :: GuardSet -> (Guard -> GuardSet) -> GuardSet
bind Bottom _ = Bottom
bind (Single s) f = f s
bind (Alt gs) f = Alt $ S.map (`bind` f) gs
bind (And gs) f = And $ S.map (`bind` f) gs

instance Refined GuardSet where
  freevs Bottom = []
  freevs (Single s) = freevs s
  freevs (Alt gs) = S.foldr (L.union . freevs) [] gs
  freevs (And gs) = S.foldr (L.union . freevs) [] gs

  rename x y = map (rename x y)

instance Binary GuardSet where
  put_ bh Bottom = put_ bh (0 :: Int)
  put_ bh (Single g) = put_ bh (1 :: Int) *> put_ bh g
  put_ bh (Alt gs) = put_ bh (2 :: Int) *> put_ bh (S.toList gs)
  put_ bh (And gs) = put_ bh (3 :: Int) *> put_ bh (S.toList gs)

  get bh = do
    i <- get bh
    case i :: Int of
      0 -> return Bottom
      1 -> Single <$> get bh
      2 -> Alt . S.fromList <$> get bh
      3 -> And . S.fromList <$> get bh

instance Outputable GuardSet where
  ppr = ppr . toList

toList :: GuardSet -> [Guard]
toList (Single g) = [g]
toList (Alt gs) = concatMap toList (S.toList gs)
toList (And gs) = S.foldr (liftM2 and) [Guard M.empty] (S.map toList gs)

-- Trivial guards
top :: GuardSet
top = Single $ Guard M.empty

-- Asserts that X contain an element from ks
dom :: [Name] -> Int -> DataType Name -> GuardSet
dom ks x d = Alt $ foldr (\k -> S.insert $ Single (Guard $ M.singleton d $ S.singleton (x, k))) S.empty ks

-- An unsatisfiable guard
isEmpty :: GuardSet -> Bool
isEmpty Bottom = True
isEmpty (Single s) = False
isEmpty (Alt gs) = all isEmpty gs
isEmpty (And gs) = any isEmpty gs

-- Replace X(d) with k in a guard and reduce
replace :: Int -> DataType Name -> K L -> GuardSet -> GuardSet
replace x d k = map go
  where
    go :: Guard -> Guard
    go (Guard g) =
      case k of
        Dom y -> Guard $ M.adjust (S.map (\(x', c) -> if x == x' then (y, c) else (x', c))) d g
        Con c _ -> Guard $ M.adjust (S.filter (/= (x, c))) d g

-- Remove guards concerning the intermediate nodes
remove :: Int -> GuardSet -> GuardSet
remove x gs =
  bind
    gs
    ( \g ->
        if x `elem` freevs g
          then Bottom
          else Single g
    )

-- -- Simplify by removing redundant guards/ reduce to minimal set
minimise :: GuardSet -> GuardSet
minimise = Alt . S.map Single . go
  where
    go :: GuardSet -> S.Set Guard
    go Bottom = S.empty
    go (Single g) = S.singleton g
    go (Alt gss) = S.foldr (\gs acc -> S.foldr minInsert acc (go gs)) S.empty gss
    go (And gss) = S.foldr (\gs -> S.map (uncurry and) . S.cartesianProduct gs) (S.singleton $ Guard M.empty) $ S.map go gss

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
applyPreds :: M.Map Int (M.Map (DataType Name) (M.Map (K L) GuardSet)) -> GuardSet -> GuardSet
applyPreds preds gs =
  bind
    gs
    ( \(Guard g) ->
        M.foldrWithKey (\d d_guards acc' -> S.foldr (\(x, k) acc'' -> go d (x, k) &&& acc'') acc' d_guards) top g
    )
  where
    go :: DataType Name -> (Int, Name) -> GuardSet
    go d (x, k) =
      case M.lookup x preds >>= M.lookup d of
        Just xd_preds ->
          M.foldrWithKey
            ( \p pg acc ->
                case p of
                  Dom y -> (dom [k] y d &&& pg) ||| acc
                  Con k' _
                    | k == k' -> pg ||| acc
                    | otherwise -> dom [k] x d ||| acc
            )
            Bottom
            xd_preds
        Nothing -> Bottom -- If there are no predecessors to X(d), we can assume it is false.
