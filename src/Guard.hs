module Guard (
  K(..),
  con,
  set,

  Guard(..),
  trivial,

  GuardSet,
  toList,
  top,
  dom,
  (|||),
  (&&&),
  replace,
  filterGuards,
  -- minimise,
) where

import Prelude hiding ((<>))
import Control.Applicative
import qualified Data.Set as S
import qualified Data.Map as M

import Types

import Name
import SrcLoc
import UniqSet
import Outputable

-- General constructors set
data K =
    Dom Int Name
  | Set (UniqSet Name) SrcSpan

con :: Name -> SrcSpan -> K
con n = Set (unitUniqSet n)

set :: [Name] -> SrcSpan -> K
set s = Set (mkUniqSet s)

instance Eq K where
  Dom x d == Dom x' d' = x == x' && d == d'
  Set s _ == Set s' _  = s == s'
  _       == _         = False

instance Ord K where
  Dom x d <= Dom x' d' = (x, d) <= (x', d')
  Set k _ <= Set k' _  = nonDetEltsUniqSet k <= nonDetEltsUniqSet k'
  Dom _ _ <= _         = True
  _       <= _         = False

instance Refined K where
  domain (Dom x _) = S.singleton x
  domain (Set _ _) = S.empty

  rename x y (Dom x' d)
    | x == x'  = Dom y d
  rename _ _ c = c

instance Outputable K where
  ppr (Dom x d)         = text "dom" <> parens (ppr x <> parens (ppr d))
  ppr (Set ks _)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (ppr "{}")
    | otherwise         = pprWithBars ppr (nonDetEltsUniqSet ks)

-- A guard, i.e. a set of constraints of the form k in (X, d)
-- Grouped by d
newtype Guard = Guard (M.Map Name (S.Set (Int, Name)))
  deriving Eq

instance Refined Guard where
  domain (Guard g)     = M.foldr (S.union . S.map fst) S.empty g
  rename x y (Guard g) = Guard $ M.map (S.map (\(x', k) -> if x == x' then (y, k) else (x', k))) g

instance Outputable Guard where
  ppr (Guard g) = sep $ punctuate and [dom k x d | (d, xks) <- M.toList g, (x, k) <- S.toList xks]
    where
      dom k x d = ppr k <+> elem <+> text "dom" <> parens (ppr x <> parens (ppr d))
      elem      = unicodeSyntax (char '∈') (text " in ")
      and       = unicodeSyntax (char '∧') (text " && ")

-- Is the guard trivially true
trivial :: Guard -> Bool
trivial (Guard m) = all S.null m

-- A collection of possible guards
-- cheaper to keep a list, and minimise at one point, than a set
newtype GuardSet = GuardSet {
  toList :: [Guard]
}

instance Refined GuardSet where
  domain (GuardSet g)     = foldr (S.union . domain) S.empty g
  rename x y (GuardSet g) = GuardSet $ fmap (rename x y) g

-- Trivial guard
top :: GuardSet
top = GuardSet [Guard $ M.empty]

-- Asserts that X contain an element from ks
dom :: S.Set Name -> Int -> Name -> GuardSet
dom ks x d = GuardSet [Guard $ M.singleton d $ S.singleton (x, k) | k <- S.toList ks]

-- Alternatives
infix 2 |||
(|||) :: GuardSet -> GuardSet -> GuardSet
GuardSet g ||| GuardSet g' = GuardSet (g ++ g')

-- Take the conjunction of every possibility
infix 3 &&&
(&&&) :: GuardSet -> GuardSet -> GuardSet
GuardSet g &&& GuardSet g' = GuardSet $ liftA2 intersect g g'
  where
    -- Combine guards
    intersect :: Guard -> Guard -> Guard
    intersect (Guard s) (Guard t) = Guard (M.unionWith S.union s t)

-- Replace k1 with k2 in a guard and reduce
replace :: Int -> Name -> K -> GuardSet -> GuardSet
replace x d cs (GuardSet gs) = GuardSet $ fmap go gs
  where
    go :: Guard -> Guard
    go (Guard g) =
      case cs of
        Dom y _  -> Guard $ M.adjust (S.map (\(x', k) -> if x == x' then (y, k) else (x', k))) d g
        Set ks _
          | [k] <- nonDetEltsUniqSet ks  -> Guard $ M.adjust (S.filter (/= (x, k))) d g
          | otherwise -> pprPanic "Non-atomic constraint!" $ ppr cs

-- Remove guards concerning the intermediate nodes
filterGuards :: S.Set Int -> GuardSet -> GuardSet
filterGuards xs (GuardSet g) = GuardSet $ filter (all (`notElem` xs) . domain) g

-- Simplify by removing redundant guards/ reduce to minimal set
-- minimise :: GuardSet -> GuardSet
-- minimise s = foldr go [] s
--  where
--    go :: Guard -> GuardSet -> GuardSet
--    go g s'
--      | any (`weaker` g) s' = s'
--      | otherwise           = L.insert g $ filter (not . weaker g) s'

-- Determine if the first guard is smaller than the second
-- weaker :: Guard -> Guard -> Bool
-- weaker (Guard g) (Guard g') = False
  -- Compare size as a short cut ?
  -- | S.size g > S.size g' = False
  -- | otherwise = all (`` g') g
