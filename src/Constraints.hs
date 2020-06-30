{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module Constraints
  ( Guard,
    singleton,
    Atomic,
    Constraint (..),
    ConstraintSet,
    insert,
    guardWith,
    saturate,
  )
where

import Binary
import Constructors
import Control.Monad.RWS hiding (guard)
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HM
import Data.Hashable
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IS
import qualified GhcPlugins as GHC
import qualified Data.List as List
import Types

-- A set of simple inclusion constraints, i.e. k in X(d), grouped by X(d)
newtype Guard
  = Guard
      { groups :: HM.HashMap (DataType GHC.Name) (GHC.UniqSet GHC.Name)
      }
  deriving (Eq)

instance Semigroup Guard where
  Guard g <> Guard g' = Guard (HM.unionWith GHC.unionUniqSets g g')

instance Monoid Guard where
  mempty = Guard mempty

instance GHC.Outputable Guard where
  ppr (Guard g) =
    GHC.pprWithCommas (\(d, k) -> GHC.hsep [GHC.ppr k, GHC.text "in", GHC.ppr d]) $
      second GHC.nonDetEltsUniqSet <$> HM.toList g

instance Binary Guard where
  put_ bh (Guard g) = put_ bh (HM.toList $ fmap GHC.nonDetEltsUniqSet g)
  get bh = Guard . HM.fromList . fmap (second GHC.mkUniqSet) <$> Binary.get bh

instance Refined Guard where
  domain (Guard g) = HM.foldrWithKey ((const . (<>)) . domain) mempty g

  rename x y (Guard g) =
    Guard
      ( HM.fromList $
          HM.foldrWithKey (\k a as -> (rename x y k, a) : as) [] g
      )

-- A guard literal
singleton :: GHC.Name -> DataType GHC.Name -> Guard
singleton k d = Guard (HM.singleton d (GHC.unitUniqSet k))

-- Remove a list of constraints from a guard
removeFromGuard :: [GHC.Name] -> DataType GHC.Name -> Guard -> Guard
removeFromGuard k d = Guard . HM.update removeFromGroup d . groups
  where
    removeFromGroup ks =
      let ks' = GHC.delListFromUniqSet ks k
       in if GHC.isEmptyUniqSet ks'
            then Nothing
            else Just ks'

type Atomic = Constraint 'L 'R

-- A pair of constructor sets
data Constraint l r
  = Constraint
      { left :: K l,
        right :: K r,
        guard :: Guard,
        srcSpan :: GHC.SrcSpan
      }

-- Disregard location in comparison
instance Eq (Constraint l r) where
  Constraint l r g _ == Constraint l' r' g' _ = l == l' && r == r' && g == g'

instance Hashable (Constraint l r) where
  hashWithSalt s c = hashWithSalt s (left c, right c, second GHC.nonDetEltsUniqSet <$> HM.toList (groups (guard c)))

instance GHC.Outputable (Constraint l r) where
  ppr a = GHC.ppr (guard a) GHC.<+> GHC.char '?' GHC.<+> GHC.ppr (left a) GHC.<+> GHC.arrowt GHC.<+> GHC.ppr (right a)

instance (Binary (K l), Binary (K r)) => Binary (Constraint l r) where
  put_ bh c = put_ bh (left c) >> put_ bh (right c) >> put_ bh (guard c) >> put_ bh (Constraints.srcSpan c)
  get bh = Constraint <$> Binary.get bh <*> Binary.get bh <*> Binary.get bh <*> Binary.get bh

instance Refined (Constraint l r) where
  domain c = domain (left c) <> domain (right c) <> domain (guard c)

  rename x y c =
    c
      { left = rename x y (left c),
        right = rename x y (right c),
        guard = rename x y (guard c)
      }

-- Is the first constraint a weaker version of the second, i.e. has a larger guard
impliedBy :: Atomic -> Atomic -> Bool
impliedBy a a'
  | left a == left a',
    right a == right a' =
    let Guard g = guard a
        Guard g' = guard a'
     in getAll $
          HM.foldMapWithKey
            ( \d ks ->
                case HM.lookup d g of
                  Nothing -> All (GHC.isEmptyUniqSet ks)
                  Just ks' -> All (GHC.uniqSetAll (`GHC.elementOfUniqSet` ks') ks)
            )
            g'
impliedBy _ _ = False

-- A constraint is trivially satisfied
tautology :: Atomic -> Bool
tautology a =
  case left a of
    Dom d ->
      case right a of
        Dom d' -> d == d'
        _ -> False
    Con k _ ->
      case right a of
        Dom d ->
          case HM.lookup d (groups (guard a)) of
            Just ks -> GHC.elementOfUniqSet k ks
            Nothing -> False
        Set ks _ -> GHC.elementOfUniqSet k ks

-- A constraint that defines a refinement variable which also appears in the guard
-- i.e. k in X(d) ? Y(d) => X(d)
-- A group of recursive constraints has an empty minimum model
recursive :: Atomic -> Bool
recursive a =
  case right a of
    Dom d ->
      case HM.lookup d (groups (guard a)) of
        Nothing -> False
        Just ks -> not (GHC.isEmptyUniqSet ks)
    Set _ _ -> False

-- Apply the saturation rules in one direction
resolve :: Atomic -> Atomic -> [Atomic]
resolve l r =
  case right l of
    Dom d ->
      -- The combined guards
      let guards = guard l <> guard r
          trans =
            case left r of
              Dom d' | d == d' -> [r {left = left l, guard = guards}] -- Trans
              _ -> []
          weak =
            case left l of
              Dom d' ->
                -- l is of shape d' <= d
                case GHC.nonDetEltsUniqSet <$> HM.lookup d (groups (guard r)) of
                  Nothing -> []
                  Just ks ->
                    let rmdGuards = removeFromGuard ks d guards
                        newGuards = foldr (\k gs -> singleton k d' <> gs) rmdGuards ks
                     in [r {guard = newGuards}] -- Substitute
              Con k _ -> [r {guard = removeFromGuard [k] d guards}] -- Weakening
       in filter (not . tautology) (trans ++ weak) -- Remove redundant constriants
    Set _ _ -> []

{-
  The lists of atomic constraints inside the set representation
  of shape, say, `[xs !! 1, xs !! 2, ..., xs !! k]` obey the
  following invariant: 
  
    for all i,j from 1 to k: 
        not (xs !! i `impliedBy` xs !! j) 
          && not (xs !! j `impliedBy` xs !! i)

  Since `impliedBy` is weaker than equality, it follows that such a 
  list does not contain duplicates. 
-}
data ConstraintSet
  = ConstraintSet
      { definite :: IntMap [Atomic],
        goal :: [Atomic]
      }
  deriving (Eq)

instance Semigroup ConstraintSet where
  cs <> ds = fold insert ds cs            

instance Monoid ConstraintSet where
  mempty = empty

instance GHC.Outputable ConstraintSet where
  ppr = fold ((GHC.$$) . GHC.ppr) GHC.empty

instance Binary ConstraintSet where
  put_ bh cs = put_ bh (IntMap.toList (definite cs)) >> put_ bh (goal cs) 
  get bh = ConstraintSet . IntMap.fromList  <$> Binary.get bh <*> (Binary.get bh) 

instance Refined ConstraintSet where
  domain cs = foldMap (foldMap domain) (definite cs) <> foldMap domain (goal cs)
  rename x y cs = fold (\a ds -> insert (rename x y a) ds) empty cs

empty :: ConstraintSet
empty = ConstraintSet { definite = IntMap.empty, goal = []}

fold :: (Atomic -> b -> b) -> b -> ConstraintSet -> b
fold f z0 cs = z2
  where
    z1 = foldr (flip (foldr f)) z0 (definite cs)
    z2 = foldr f z1 (goal cs)

mapAction :: Monad m => (Atomic -> m ()) -> ConstraintSet -> m ()
mapAction f cs = fold (\a b -> f a >> b) (return ()) cs

insert' :: Atomic -> ConstraintSet -> (ConstraintSet, Bool)
insert' a cs =
  case right a of
    Dom (Base _) -> (cs, False) -- Ignore constraints concerning base types
    Dom (Inj x _) -> 
      if any (a `impliedBy`) (IntMap.findWithDefault [] x (definite cs)) then
        (cs, False) 
      else 
        let reducedDefs = 
              filter (not . (`impliedBy` a)) (IntMap.findWithDefault [] x (definite cs))
        in (cs { definite = IntMap.insert x (a:reducedDefs) (definite cs) }, True)
    Set _ _ -> 
      if any (a `impliedBy`) (goal cs) then
        (cs, False)
      else
        let reducedGls = 
              filter (not . (`impliedBy` a)) (goal cs)
        in (cs { goal = a : reducedGls }, True)

-- Add an atomic constriant to the set
-- ensuring to maintain the invariant
insert :: Atomic -> ConstraintSet -> ConstraintSet
insert a = fst . insert' a

-- Remove a constraint from a set
remove :: Atomic -> ConstraintSet -> ConstraintSet
remove a cs =
  case right a of
    Dom (Base _) -> cs -- Ignore constraints concerning base types
    Dom (Inj x _) -> cs {definite = IntMap.update deleteA x (definite cs)}
    Set _ _ -> cs {goal = List.delete a (goal cs)}
  where
    deleteA as =
      let as' = List.delete a as
       in if List.null as'
            then Nothing
            else Just as'

-- Add a guard to every constraint
guardWith :: Guard -> ConstraintSet -> ConstraintSet
guardWith g cs =
  cs
    { definite = IntMap.map (List.map go) (definite cs),
      goal = map go (goal cs)
    }
  where
    go a = a {guard = g <> guard a}

-- Apply the saturation rules and remove intermediate variables until a fixedpoint is reached
saturate :: IS.IntSet -> ConstraintSet -> ConstraintSet
saturate is cs
  | IS.null (domain cs IS.\\ is) = cs
  | otherwise = do
    let i = IS.findMin (domain cs IS.\\ is)
    case runRWS (saturateF i) () cs of
      ((), cs', Any True) -> saturate is cs' -- New constriant have been found, i.e. not a fixedpoint
      ((), cs', Any False) -> saturate (IS.insert i is) (eliminate i cs')

-- Remove constraints concerning a particular refinement variable
eliminate :: Int -> ConstraintSet -> ConstraintSet
eliminate i cs =
  ConstraintSet
    { definite =
        IntMap.mapMaybeWithKey
          ( \x s ->
              if i == x
                then Nothing
                else Just $ List.filter (IS.notMember i . domain) s
          )
          (definite cs),
      goal = filter (IS.notMember i . domain) (goal cs)
    }

-- One step consequence operator for saturation rules concerning a particular refinement variable
saturateF :: Int -> RWS () Any ConstraintSet ()
saturateF i =
  -- Lookup constraints with x in the head
  gets (IntMap.lookup i . definite) >>= \case
    Just cs
      -- If there are only recursive clauses the minimum model is empty
      | not (all recursive cs) ->
        mapM_ resolveAllWith cs
    _ -> return ()
  where
    addResolvant r = do
      ds <- Control.Monad.RWS.get 
      let (ds', b) = insert' r ds
      Control.Monad.RWS.put ds'
      tell (Any b)
    resolveAllWith c = do
      ds <- Control.Monad.RWS.get
      mapAction (mapM_ addResolvant . resolve c) ds
      unless (recursive c) $ modify (remove c)
