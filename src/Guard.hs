module Guard (
  K(..),
  con,
  safe,

  Guard,

  GuardSet,
  toList,
  top,
  dom,
  isEmpty,
  (|||),
  (&&&),
  replace,
  filterGuards,
  -- minimise,
) where

import Prelude hiding ((<>))
import Control.Applicative hiding (empty)
import qualified Data.Set as S
import qualified Data.Map as M

import Types

import Name
import SrcLoc
import Binary
import UniqSet
import Outputable hiding (isEmpty)

-- General constructors set
data K =
    Dom Int Name
  | Set (UniqSet Name) SrcSpan

-- Disregard srcspan in comparison
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

instance Binary K where
  put_ bh (Dom x d) = put_ bh (0 :: Int) >> put_ bh x >> put_ bh d
  put_ bh (Set s l) = put_ bh (1 :: Int) >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> do
        x <- get bh
        d <- get bh
        return (Dom x d)
      1 -> do
        s <- get bh
        l <- get bh
        return (Set (mkUniqSet s) l)

-- Convenient smart constructors
con :: Name -> SrcSpan -> K
con = Set . unitUniqSet

-- A constraint that has an atomic form
safe :: K -> K -> Bool
safe (Set k _) (Set k' _) = uniqSetAll (`elementOfUniqSet` k') k
safe _ _                  = True

-- A guard, i.e. a set of constraints of the form k in (X, d)
-- Grouped by d
newtype Guard = Guard (M.Map Name (S.Set (Int, Name)))
  deriving Eq

instance Refined Guard where
  domain (Guard g)     = M.foldr (S.union . S.map fst) S.empty g
  rename x y (Guard g) = Guard $ M.map (S.map (\(x', k) -> if x == x' then (y, k) else (x', k))) g

instance Outputable Guard where
  ppr (Guard g)
    | all S.null g = empty
    | otherwise    = sep (punctuate and [dom k x d | (d, xks) <- M.toList g, (x, k) <- S.toList xks]) <+> char '?'
    where
      dom k x d = ppr k <+> elem <+> text "dom" <> parens (ppr x <> parens (ppr d))
      elem      = unicodeSyntax (char '∈') (text " in ")
      and       = unicodeSyntax (char '∧') (text " && ")

instance Binary Guard where
  put_ bh (Guard m) = put_ bh [ (n, S.toList s) | (n ,s) <- M.toList m]
  get bh = do
    l <- get bh
    return $ Guard $ M.fromList [ (n, S.fromList l') | (n, l') <- l]

-- A collection of possible guards
-- cheaper to keep a list, and minimise at one point, than a set
newtype GuardSet = GuardSet {
  toList :: [Guard]
}

instance Refined GuardSet where
  domain (GuardSet g)     = foldr (S.union . domain) S.empty g
  rename x y (GuardSet g) = GuardSet $ fmap (rename x y) g

instance Binary GuardSet where
  put_ bh = put_ bh . toList
  get  bh = GuardSet <$> get bh

-- Trivial guard
top :: GuardSet
top = GuardSet [Guard M.empty]

-- Asserts that X contain an element from ks
dom :: S.Set Name -> Int -> Name -> GuardSet
dom ks x d = GuardSet [Guard $ M.singleton d $ S.singleton (x, k) | k <- S.toList ks]

-- An unsatisfiable guard
isEmpty :: GuardSet -> Bool
isEmpty = null . toList

-- Alternatives
infix 2 |||
(|||) :: GuardSet -> GuardSet -> GuardSet
GuardSet g ||| GuardSet g' = GuardSet (g ++ g')

-- Take the conjunction of every possibility
infix 3 &&&
(&&&) :: GuardSet -> GuardSet -> GuardSet
GuardSet g &&& GuardSet g' = GuardSet $ liftA2 intersect g g'
  where
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
