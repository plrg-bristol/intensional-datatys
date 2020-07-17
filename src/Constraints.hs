{-# OPTIONS_HADDOCK ignore-exports #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- the Foldable instance for GHC.UniqFM is an orphan
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

{-|
    Atomic constraints and sets of atomic constraints, represented as antichains.  Saturation and restriction. 
-}
module Constraints
  ( 
    Atomic,
    Constraint (..),
    ConstraintSet,
    insert,
    guardWith,
    saturate,
    size,
  )
where

import Binary
import Data.Foldable
import Control.Monad.State (State)
import Data.IntMap (IntMap)
import Data.HashMap.Strict (HashMap)
import Data.IntSet (IntSet)
import qualified Control.Monad.State as State
import qualified Data.HashMap.Strict as HashMap
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import qualified GhcPlugins as GHC
import qualified Control.Monad as Monad

import Types
import Constructors
import Guard (Guard)
import qualified Guard

{-|
    The type of constraints @c@ of shape @guard c@ ? @left c@ ⊆ @right c@ that originated from the 
    source at @srcSpan c@.
-}
type Atomic = Constraint 'L 'R

data Constraint l r
  = Constraint
      { left :: K l,
        right :: K r,
        guard :: Guard,
        srcSpan :: GHC.SrcSpan
      }

instance Eq (Constraint l r) where
  -- Disregard location in comparison
  Constraint l r g _ == Constraint l' r' g' _ = l == l' && r == r' && g == g'

instance GHC.Outputable (Constraint l r) where
  ppr a = GHC.ppr (guard a) GHC.<+> GHC.char '?' GHC.<+> GHC.ppr (left a) GHC.<+> GHC.arrowt GHC.<+> GHC.ppr (right a)

instance (Binary (K l), Binary (K r)) => Binary (Constraint l r) where
  put_ bh (Constraint l r g ss) = put_ bh l >> put_ bh r >> put_ bh g >> put_ bh ss
  get bh = Constraint <$> Binary.get bh <*> Binary.get bh <*> Binary.get bh <*> Binary.get bh

instance Refined (Constraint l r) where
  domain c = domain (left c) <> domain (right c) <> domain (guard c)
  rename x y c =
    c
      { left = rename x y (left c),
        right = rename x y (right c),
        guard = rename x y (guard c)
      }

{-|
    Given two atomic constraints @a@ and @b@, @a `impliedBy` b@ just
    if @a@ and @b@ have the same body and the guard of @a@ is implied
    by the guard of @b@.
-}
impliedBy :: Atomic -> Atomic -> Bool
impliedBy a a' =
  left a == left a' && right a == right a' && guard a `Guard.impliedBy` guard a'

{-|
    Given an atomic constraint @a@, @tautology a@ just if @a@ is satisfied in 
    every assignment.
-}
tautology :: Atomic -> Bool
tautology a =
  case left a of
    Dom d ->
      case right a of
        Dom d' -> d == d'
        _ -> False
    Con k _ ->
      case right a of
        Dom (Inj x d) ->
          case Guard.lookup x d (guard a) of
            Just ks -> GHC.elementOfUniqSet k ks
            Nothing -> False
        Set ks _ -> GHC.elementOfUniqSet k ks
        _        -> error "[ERROR] Unexpected right atom"


{-|
    Given atomic constraints @a@ and @b@, @resolve a b@ is:

      * @Nothing@ if the resolvant of @a@ and @b@ is a tautology
      * @Just r@ otherwise, where @r@ is the resolvant as an atomic constraint
-}
resolve :: Atomic -> Atomic -> Maybe Atomic
resolve l r =
    -- simplify the the new constraint if it's body contains two literals
    case (left newR, right newR) of
      (Con k _, Set ks _) | GHC.elementOfUniqSet k ks -> Nothing
      (Con _ _, Set _  s) | otherwise                 -> Just (newR { right = Set mempty s})
      (_,       _       )                             -> Just newR
  where
    weaken x d y g = 
      -- weaken x(d) in g to y(d)
      case Guard.lookup x d g of
        Just ms | ks <- GHC.nonDetEltsUniqSet ms -> 
          Just (Guard.singleton ks y d <> Guard.deleteAll ks x d g)
        Nothing -> Nothing
    satisfy x d k g =
      -- satisfy x(d) in g by k
      case Guard.lookup x d g of
        Just ks | k `GHC.elementOfUniqSet` ks -> Just (Guard.delete k x d g)
        _                                     -> Nothing
    mbNewGuard = 
      -- create a new guard by modifying the old one according to
      -- saturation and weakening (ignoring l's guard, for now)
      case (left l, right l) of 
        (Dom (Inj y _), Dom (Inj x d)) -> weaken x d y (guard r)
        (Con k _,       Dom (Inj x d)) -> satisfy x d k (guard r)
        (_,             _            ) -> Nothing
    mbNewLeft = 
      -- apply transitivity, or not (ignoring l's guard, for now)
      case (right l, left r) of
        (Dom (Inj x d), Dom (Inj z d')) | z == x && d == d' -> Just (left l)
        (_,             _            )                      -> Nothing
    newR = 
      -- determine whether or not to attach a single copy of l's guards
      case (mbNewGuard, mbNewLeft) of
      (Just grd, Just lft) -> r { left = lft, guard = guard l <> grd }
      (Just grd, Nothing ) -> r { guard = guard l <> grd }
      (Nothing,  Just lft) -> r { left = lft, guard = guard l <> guard r }
      (Nothing,  Nothing ) -> r
      
-- We only use ConstraintSetF with Atomic so far, but it is worth making
-- this structure clear to derive Foldable etc
-- TODO: Remove these hashmaps in favour of IntMaps
data ConstraintSetF a
  = ConstraintSetF
      { 
        -- constraints of the form GS ? Y(d) <= Y(d)
        -- represented as X -> (d -> (Y -> GS)) 
        definiteVV :: IntMap (GHC.NameEnv (HashMap Int [a])),
        -- constraints of the form GS ? k in X(d)
        -- represented as X -> (d -> (k -> GS))
        definiteKV :: IntMap (GHC.NameEnv (HashMap GHC.Name [a])),
        -- constraints of the form G ? S1 <= {k1,...,km}
        -- represented as a list
        goal :: [a]
      }
  deriving (Eq, Functor, Foldable)

-- | The type of antichains of atomic constraints.
type ConstraintSet = ConstraintSetF Atomic

instance Foldable GHC.UniqFM where
  foldr = GHC.foldUFM 

{-|
    Given a list of atomic constraints @cs@, @fromList cs@ is
    largest antichain contained in @cs@
-}
fromList :: [Atomic] -> ConstraintSet
fromList = foldr insert empty

instance Semigroup ConstraintSet where
  cs <> ds = foldr insert ds cs

instance Monoid ConstraintSet where
  mempty = empty

instance GHC.Outputable ConstraintSet where
  ppr = foldr ((GHC.$$) . GHC.ppr) GHC.empty

instance Binary ConstraintSet where
  put_ bh = put_ bh . toList
  get bh = fromList <$> get bh

instance Refined ConstraintSet where
  domain = foldMap domain
  rename x y = -- this may create non-normalised constraint sets
    foldl' (\ds a -> unsafeInsert (rename x y a) ds) empty


{-|
    @empty@ is the empty constraint set
-}
empty :: ConstraintSet
empty =
  ConstraintSetF
    { 
      definiteVV = mempty,
      definiteKV = mempty,
      goal = []
    }

{-| 
    When @cs@ is a constraint set, @size cs@ is its cardinality.
-}
size :: ConstraintSet -> Int
size = foldl' (\sz _ -> 1 + sz) 0

{-| 
    When @a@ is an atomic constraint and @cs@ a constraint set,
    @unsafeInsert a cs@ is the constraint set obtained by inserting
    @a@ into @cs@.  
    
    Note: @unsafeInsert a cs@ may not be an antichain even if @cs@ is.
-}
unsafeInsert :: Atomic -> ConstraintSet -> ConstraintSet
unsafeInsert a cs =
  case (left a, right a) of
    (Dom (Inj x _), Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (definiteVV cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] x hm
       in cs {definiteVV = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert x (a : as) hm)) (definiteVV cs)}
    (Con k _, Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (definiteKV cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] k hm
       in cs {definiteKV = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert k (a : as) hm)) (definiteKV cs)}
    (_, Set _ _) -> cs {goal = a : goal cs}
    (_, _) -> cs

{-| 
    When @a@ is an atomic constraint and @cs@ is a constraint antichain 
    @insert a cs@ is: 
    
      * @Nothing@ just if @a@ is already implied by some constraint in @cs@.
      * @Just ds@ otherwise, where @ds@ is the constraint antichain obtained 
        by inserting @a@ into @cs@. Note: @ds@ may be smaller than @cs@.
-}
insert' :: Atomic -> ConstraintSet -> Maybe ConstraintSet
insert' a cs | not (tautology a) =
  case (left a, right a) of
    (Dom (Inj x _), Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (definiteVV cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] x hm
       in fmap (\as' -> cs {definiteVV = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert x as' hm)) (definiteVV cs)}) (maintain as)
    (Con k _, Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (definiteKV cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] k hm
       in fmap (\as' -> cs {definiteKV = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert k as' hm)) (definiteKV cs)}) (maintain as)
    (_, Set _ _) ->
      fmap (\as' -> cs {goal = as'}) (maintain (goal cs))
    (_, _) -> Nothing -- Ignore constraints concerning base types
  where
    maintain ds =
      if any (a `impliedBy`) ds then Nothing else Just (a : filter (not . (`impliedBy` a)) ds)
insert' _ _ = Nothing

{-| 
    When @a@ is an atomic constraint and @cs@ is a constraint antichain 
    @insert a cs@ is the constraint antichain obtained by inserting @a@
    into @cs@.  Note: the antichain @insert a cs@ may be smaller than @cs@.
-}
insert :: Atomic -> ConstraintSet -> ConstraintSet
insert a cs = Maybe.fromMaybe cs (insert' a cs)

{-|
    When @g@ is a guard and @cs@ a set of constraints, @guardWith g cs@ is 
    the set of constraints obtained from @cs@ by appending @g@ to every guard
    of every constraint.
-}
guardWith :: Guard -> ConstraintSet -> ConstraintSet
guardWith g cs =
  cs { 
      definiteVV = IntMap.map (GHC.mapUFM (HashMap.map (List.map go))) (definiteVV cs),
      definiteKV = IntMap.map (GHC.mapUFM (HashMap.map (List.map go))) (definiteKV cs),
      goal = map go (goal cs)
    }
  where
    go a = a {guard = g <> guard a}

{-|
    When @iface@ is a set of interface variables and @cs@ is a constraint set, 
    @saturate iface cs@ is the constraint set obtained from @cs@ by saturation
    and restriction to @iface@.
-}
saturate :: IntSet -> ConstraintSet -> ConstraintSet
saturate iface cs  = 
    es
  where
    allExt xs = xs `IntSet.isSubsetOf` iface
    ls = foldl' (\ms c -> if allExt (domain (left c) <> domain (guard c)) then unsafeInsert c ms else ms) mempty cs
    ds = snd $ State.execState (fix iface) (ls, cs)
    es = foldl' (\fs a -> if allExt $ domain a then unsafeInsert a fs else fs) mempty ds

{-| 
    When @exts@ is the set of interface variables @fix exts@ is the
    stateful computation that transforms an initial state @(ls, rs)@
    where @ls@ are all unit constraints modulo @exts@ and @ls@ is contained
    in @rs@, into a final state @(ls', rs')@ in which @ls@ is empty and
    @rs'@ is the saturation of @rs@.
-}
fix :: IntSet -> State (ConstraintSet, ConstraintSet) ()
fix exts =
  do  (ls, _) <- State.get
      Monad.unless (null ls) $ saturate1 exts >> fix exts

{-| 
     When @exts@ is a set of interface variables @saturate1 exts@ is the 
     stateful computation that takes an initial state @(ls, rs)@ consisting
     of a pair of constraint sets with @ls@ being unit clauses modulo `exts`
     and @ls@ being contained in @rs@ to a final state @(ls', rs')@ in which:

       *  @ls'@ is those constraints in @rs'@ that are not in @rs@ and which 
          are unit modulo @exts@.
       *  @rs'@ contains all the constraints obtained from @rs@ by resolving 
          on the left with each clauses from @ls@ once.
-}
saturate1 :: IntSet -> State (ConstraintSet, ConstraintSet) ()
saturate1 exts =
    do  (ls, rs) <- State.get
        State.put (mempty, rs)
        Monad.forM_ ls $ \l ->
          do  -- We immediately get the current state to allow
              -- for two left constraints to be applied to the
              -- same right constraint
              rs' <- State.gets snd
              Monad.forM_ rs' $ \r -> 
                  addResolvant (resolve l r)
  where
    addResolvant Nothing  = return ()
    addResolvant (Just r) =
      do  let bodyVars = domain (left r) <> domain (guard r)
          let varsAllExts = bodyVars `IntSet.isSubsetOf` exts
          (ls, rs) <- State.get
          case insert' r rs of
            Nothing -> return ()
            Just rs' -> 
              -- Insert the new constraint into ls only if it is a 
              -- unit clause modulo externals.
              State.put (if varsAllExts then insert r ls else ls, rs')

