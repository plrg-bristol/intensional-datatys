{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}

module Constraints (
  Side(..),
  K(..),
  safe,
  toAtomic,

  Guard,

  GuardSet,
  toList,
  top,
  bot,
  dom,
  isEmpty,
  (|||),
  (&&&),
  applyPreds,
) where

import Prelude hiding ((<>))
import Data.Hashable
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List as L

import Name
import SrcLoc hiding (L)
import Binary
import Unique
import UniqSet
import Outputable hiding (isEmpty)

import Types

-- Atomic constructors set
data Side = L | R

data K (s :: Side) where
  Dom :: Int -> K s
  Set :: UniqSet Name -> SrcSpan -> K R
  Con :: Name -> SrcSpan -> K L

-- Disregard srcspan in comparison
instance Eq (K s) where
  Dom x   == Dom x'   = x == x'
  Set s _ == Set s' _ = s == s'
  Con k _ == Con k' _ = k == k'
  _       == _        = False

instance Ord (K s) where
  Dom x   <= Dom x'   = x <= x'
  Set k _ <= Set k' _ = nonDetEltsUniqSet k <= nonDetEltsUniqSet k'
  Con k _ <= Con k' _ = k <= k'
  Dom _   <= _        = True
  _       <= _        = False

instance Refined (K s) where
  freevs (Dom x)   = [x]
  freevs (Con _ _) = []
  freevs (Set _ _) = []

  rename x y (Dom x')
    | x == x'  = Dom y
  rename _ _ c = c

instance Outputable (K s) where
  ppr (Dom x)           = text "dom" <> parens (ppr x)
  ppr (Con k _)         = ppr k
  ppr (Set ks _)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (ppr "{}")
    | otherwise         = pprWithBars ppr (nonDetEltsUniqSet ks)

instance Binary (K L) where
  put_ bh (Dom x)   = put_ bh False >> put_ bh x
  put_ bh (Con k l) = put_ bh True  >> put_ bh k >> put_ bh l

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
  put_ bh (Dom x)   = put_ bh False >> put_ bh x
  put_ bh (Set s l) = put_ bh True  >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh = do
    n <- get bh
    if n
      then do
        x <- get bh
        return (Dom x)
      else do
        s <- get bh
        l <- get bh
        return (Set (mkUniqSet s) l)

instance Hashable (K s) where
  hashWithSalt s (Dom x)    = hashWithSalt s x
  hashWithSalt s (Set ks _) = hashWithSalt s (getKey <$> nonDetKeysUniqSet ks)
  hashWithSalt s (Con k _)  = hashWithSalt s (getKey $ getUnique k)

-- Is a pair of constructor sets safe
safe :: K l -> K r -> Bool
safe (Set ks _) (Set ks' _) = uniqSetAll (`elementOfUniqSet` ks') ks
safe (Con k _) (Set ks _)   = elementOfUniqSet k ks
safe (Set ks _) (Con k _)   = nonDetEltsUniqSet ks == [k]
safe _ _                    = True

-- Convert constraint to atomic form
toAtomic :: K l -> K r -> Maybe [(K L, K R)]
toAtomic (Dom x) (Dom y)
  | x /= y     = Just [(Dom x, Dom y)]
toAtomic (Dom x) (Set k l)
               = Just [(Dom x, Set k l)]
toAtomic (Set ks l) (Dom x)
               = Just [(Con k l, Dom x) | k <- nonDetEltsUniqSet ks]
toAtomic (Con k l) (Dom x)
               = Just [(Con k l, Dom x)]
toAtomic k1 k2
  | safe k1 k2 = Just []
  | otherwise  = Nothing

-- A guard, i.e. a set of constraints of the form k in (X, d)
-- Grouped by d
newtype Guard = Guard (M.Map Name (S.Set (Int, Name)))
  deriving (Eq, Ord)

instance Refined Guard where
  freevs (Guard g)     = S.toList $ M.foldr (S.union . S.map fst) S.empty g
  rename x y (Guard g) = Guard $ fmap (S.map (\(x', k) -> if x == x' then (y, k) else (x', k))) g

instance Outputable Guard where
  ppr (Guard g)
    | all S.null g = empty
    | otherwise    = sep (punctuate and [dom k x d | (d, xks) <- M.toList g, (x, k) <- S.toList xks]) <+> char '?'
    where
      dom k x d = ppr k <+> elem <+> text "dom" <> parens (ppr x <> parens (ppr d))
      elem      = unicodeSyntax (char '∈') (text "in")
      and       = unicodeSyntax (char '∧') (text " & ")

instance Binary Guard where
  put_ bh (Guard m) = put_ bh [ (n, S.toList s) | (n ,s) <- M.toList m]
  get bh = do
    l <- get bh
    return $ Guard $ M.fromList [ (n, S.fromList l') | (n, l') <- l]

-- A collection of possible guards
-- Would it be cheaper to keep a list?
newtype GuardSet = GuardSet (S.Set Guard)
  deriving Eq

instance Refined GuardSet where
  freevs (GuardSet g)     = foldr (L.union . freevs) [] g
  rename x y (GuardSet g) = GuardSet $ S.map (rename x y) g

instance Binary GuardSet where
  put_ bh (GuardSet g) = put_ bh $ S.toList g
  get  bh = GuardSet . S.fromList <$> get bh

instance Outputable GuardSet where
  ppr = ppr . toList

toList :: GuardSet -> [Guard]
toList (GuardSet g) = S.toList g

-- Trivial guards
top, bot :: GuardSet
top = GuardSet $ S.singleton $ Guard M.empty
bot = GuardSet S.empty

-- Asserts that X contain an element from ks
dom :: S.Set Name -> Int -> Name -> GuardSet
dom ks x d = GuardSet (S.map (\k -> Guard $ M.singleton d $ S.singleton (x, k)) ks)

-- An unsatisfiable guard
isEmpty :: GuardSet -> Bool
isEmpty (GuardSet g) = S.null g

-- Alternatives
-- Assume rhs is already minimal
infix 2 |||
(|||) :: GuardSet -> GuardSet -> GuardSet
{-# INLINE (|||) #-}
GuardSet g' ||| gs = S.foldr go gs g'
  where
   go :: Guard -> GuardSet -> GuardSet
   go g (GuardSet gs')
     | any (`weaker` g) gs' = GuardSet gs'
     | otherwise            = GuardSet $ S.insert g $ S.filter (not . weaker g) gs'

-- Take the conjunction of every possibility
infix 3 &&&
(&&&) :: GuardSet -> GuardSet -> GuardSet
{-# INLINE (&&&) #-}
GuardSet gs &&& GuardSet gs' = minimise $ GuardSet $ S.map (\(Guard s, Guard t) -> Guard (M.unionWith S.union s t)) $ S.cartesianProduct gs gs'

-- Replace X(d) with k in a guard and reduce
replace :: Int -> Name -> K L -> GuardSet -> GuardSet
replace x d k (GuardSet gs) = GuardSet $ S.map go gs
  where
    go :: Guard -> Guard
    go (Guard g) =
      case k of
        Dom y   -> Guard $ M.adjust (S.map (\(x', c) -> if x == x' then (y, c) else (x', c))) d g
        Con c _ -> Guard $ M.adjust (S.filter (/= (x, c))) d g

-- Remove guards concerning the intermediate nodes
remove :: Int -> GuardSet -> GuardSet
remove x (GuardSet gs) = GuardSet $ S.filter (notElem x . freevs) gs

-- Simplify by removing redundant guards/ reduce to minimal set
minimise :: GuardSet -> GuardSet
{-# INLINE minimise #-}
minimise gs = gs ||| bot

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
applyPreds :: M.Map Int (M.Map Name (M.Map (K L) GuardSet)) -> GuardSet -> GuardSet
applyPreds preds (GuardSet gs) = S.foldr (\(Guard g) acc -> M.foldrWithKey (\d d_guards acc' -> S.foldr (\(x, k) acc'' -> go d (x, k) &&& acc'') acc' d_guards) top g ||| acc) bot gs
  where
    go :: Name -> (Int, Name) -> GuardSet
    go d (x, k) =
      case M.lookup x preds >>= M.lookup d of
        Just xd_preds -> M.foldrWithKey (\p pg acc ->
          case p of
            Dom y -> (dom (S.singleton k) y d &&& pg) ||| acc
            Con k' _
              | k == k'   -> pg ||| acc
              | otherwise -> dom (S.singleton k) x d ||| acc
          ) bot xd_preds
        Nothing -> bot -- If there are no predecessors to X(d), we can assume it is false.
