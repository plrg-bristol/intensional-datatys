{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
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
    size,
  )
where

import Binary
import Constructors
import Control.Monad.RWS (RWS)
import qualified Control.Monad.RWS as RWS
import Control.Monad.State (State)
import qualified Control.Monad.State as State
import Data.Bifunctor
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.IntSet as IS
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import Data.Monoid
import Debug.Trace
import qualified GhcPlugins as GHC
import Types
import Ubiq

data Named a = Named {toPair :: (GHC.Name, a)}
  deriving (Eq, Functor)

instance Semigroup a => Semigroup (Named a) where
  Named (n, ks1) <> Named (_, ks2) = Named (n, ks1 <> ks2)

instance GHC.Uniquable (Named a) where
  getUnique (Named (n, _)) = GHC.getUnique n

instance Binary a => Binary (Named a) where
  put_ bh = put_ bh . toPair
  get bh = Named <$> Binary.get bh

-- A set of simple inclusion constraints, i.e. k in X(d), grouped by X(d)
newtype Guard
  = Guard
      { groups :: IntMap (GHC.NameEnv (Named (GHC.UniqSet GHC.Name)))
      }
  deriving (Eq)

instance Semigroup Guard where
  Guard g <> Guard g' = Guard (IntMap.unionWith (GHC.plusUFM_C (<>)) g g')

instance Monoid Guard where
  mempty = Guard mempty

instance GHC.Outputable Guard where
  ppr (Guard g) =
    let processInner xs =
          foldr (\(x, ml) acc -> map ((,) x) ml ++ acc) [] xs
     in GHC.pprWithCommas (\(x, (d, ks)) -> GHC.hsep [GHC.ppr ks, GHC.text "in", GHC.ppr (Inj x d)])
          $ fmap (second (second GHC.nonDetEltsUniqSet)) . processInner
          $ second (fmap toPair . GHC.nameEnvElts) <$> IntMap.toList g

toList :: Guard -> [(Int, GHC.Name, GHC.Name)]
toList (Guard g) =
  [ (x, d, k)
    | (x, kds) <- IntMap.toList g,
      (d, ks) <- toPair <$> GHC.nameEnvElts kds,
      k <- GHC.nonDetEltsUniqSet ks
  ]

fromList :: [(Int, GHC.Name, GHC.Name)] -> Guard
fromList = foldMap (\(x, d, k) -> singleton k (Inj x d))

instance Binary Guard where
  put_ bh = put_ bh . toList
  get bh = fromList <$> get bh

instance Refined Guard where
  domain (Guard g) = IntMap.keysSet g

  rename x y (Guard g) =
    Guard
      ( IntMap.fromList $
          IntMap.foldrWithKey (\k a as -> (if k == x then y else k, a) : as) [] g
      )

guardLookup :: DataType GHC.Name -> Guard -> Maybe (GHC.UniqSet GHC.Name)
guardLookup (Inj x d) (Guard g) =
  fmap (snd . toPair) . flip GHC.lookupUFM d =<< IntMap.lookup x g

-- A guard literal
-- Ignorning possibly trivial guards (e.g. 1-constructor types has already
-- happened in InferM.branch)
singleton :: GHC.Name -> DataType GHC.Name -> Guard
singleton k (Inj x d) =
  Guard (IntMap.singleton x (GHC.unitNameEnv d (Named (d, GHC.unitUniqSet k))))

guardsFromList :: [GHC.Name] -> DataType GHC.Name -> Guard
guardsFromList ks (Inj x d) = foldr (\k gs -> singleton k (Inj x d) <> gs) mempty ks

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

-- instance Hashable (Constraint l r) where
--   hashWithSalt s c = hashWithSalt s (left c, right c, second GHC.nonDetEltsUniqSet <$> HM.toList (groups (guard c)))

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

-- Is the first constraint a weaker version of the second, i.e. has a larger guard
impliedBy :: Atomic -> Atomic -> Bool
impliedBy a a' =
  left a == left a' && right a == right a' && guard a `gimpliedBy` guard a'

gimpliedBy :: Guard -> Guard -> Bool
gimpliedBy a a' =
  let Guard g = a
      Guard g' = a'
      keyInclusion (Named (_, u1)) (Named (_, u2)) =
        {-# SCC keyInclusion #-}
        IntMap.isSubmapOfBy (\_ _ -> True) (GHC.ufmToIntMap $ GHC.getUniqSet u1) (GHC.ufmToIntMap $ GHC.getUniqSet u2)
   in {-# SCC "OuterLoop" #-} IntMap.isSubmapOfBy (\u1 u2 -> {-# SCC "InnerLoop" #-} IntMap.isSubmapOfBy keyInclusion (GHC.ufmToIntMap u1) (GHC.ufmToIntMap u2)) g' g

--  in getAll $
--       HM.foldMapWithKey
--         ( \d ks ->
--             case HM.lookup d g of
--               Nothing -> All (GHC.isEmptyUniqSet ks)
--               Just ks' -> All (GHC.uniqSetAll (`GHC.elementOfUniqSet` ks') ks)
--         )
--         g'

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
          case guardLookup d (guard a) of
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
      case guardLookup d (guard a) of
        Nothing -> False
        Just ks -> not (GHC.isEmptyUniqSet ks)
    Set _ _ -> False

-- Apply all possible lhs constraints to a in all possible ways using the saturation rules
resolve' :: IS.IntSet -> ConstraintSet -> Atomic -> [Atomic]
resolve' dom cs a = new --trace ("Totalling:" ++ show (length new)) new
  where
    -- Turn the guard into a list of shape [(x,[(d1,[k1,...]),...]),...]
    guardAsList = fmap (second (fmap toPair . GHC.nameEnvElts)) $ IntMap.toList (groups $ guard a)
    -- We need to unpack it into atomic propositions [(x,d1,k1),...]
    easierGuardList1 = concatMap (\(x, ds) -> [(x, d, GHC.nonDetEltsUniqSet ks) | (d, ks) <- ds]) guardAsList
    -- easierGuardList2 = concatMap (\(x,ds) -> [ (x,d,k) | (d,k) <- concatMap (\(d,ks) -> [(d,k) | k <- GHC.nonDetEltsUniqSet ks ]) ds]) guardAsList
    -- Map each entry `k in x(d)` to a list of possible resolvants
    guardAlternatives = map getAlts easierGuardList1
      where
        getAlts (x, d, ks) =
          let -- Substitutions
              ne = IntMap.findWithDefault mempty x (definite cs)
              hm = GHC.lookupWithDefaultUFM ne mempty d
              as = HashMap.toList hm
              -- Weakenings
              ne' = IntMap.findWithDefault mempty x (indefinite cs)
              hm' = GHC.lookupWithDefaultUFM ne' mempty d
           in if not (x `IS.member` dom)
                then [guardsFromList ks (Inj x d)] -- x is not in the domain of resolution
                else
                  concatMap (\((y, _), bs) -> [guardsFromList ks (Inj y d) <> guard b | b <- bs]) as
                    ++ (map mconcat $ sequence (map (\k -> map guard (HashMap.findWithDefault [] k hm')) ks))
    -- Note: if one of the guards involves x(d) and x is in the domain but there are no
    -- resolvers with x(d) in the head, then prodOfAlts will be empty and so we will return []
    -- This corresponds to setting x(d) to empty, which falisfies the guard and renders the
    -- constraint trivial.
    impSequenceW :: (a -> Guard -> Guard) -> [[a]] -> [Guard]
    impSequenceW _ [] = [mempty]
    impSequenceW f (ma : mas) =
      foldl addToResult [] [(a, as) | a <- ma, as <- allMas]
      where
        allMas = impSequenceW f mas
        addToResult gs (a, as) =
          let g = f a as in if any (g `gimpliedBy`) gs then gs else g : filter (not . (`gimpliedBy` g)) gs
    prodOfAlts = impSequenceW (<>) guardAlternatives
    -- Resolve `left a` with all possibilities
    addOrNot (b, g) rs =
      let c = a {left = left b, guard = guard b <> g}
       in if any (c `impliedBy`) rs then rs else c : filter (not . (`impliedBy` c)) rs
    new = foldr addOrNot [] $ [(x, y) | x <- bs, y <- prodOfAlts]
      where
        bs =
          case left a of
            Con _ _ -> [a]
            Dom (Inj x d) ->
              let -- Transitivity
                  ne = IntMap.findWithDefault mempty x (definite cs)
                  hm = GHC.lookupWithDefaultUFM ne mempty d
                  ne' = IntMap.findWithDefault mempty x (indefinite cs)
                  hm' = GHC.lookupWithDefaultUFM ne' mempty d
               in if not (x `IS.member` dom) then [a] else concat $ HashMap.elems hm ++ HashMap.elems hm'
            _ -> GHC.pprPanic "Not possible to have any other kind of constructor here" GHC.empty

data ConstraintSet
  = ConstraintSet
      { definite :: IntMap (GHC.NameEnv (HashMap (Int, GHC.Name) [Atomic])),
        indefinite :: IntMap (GHC.NameEnv (HashMap GHC.Name [Atomic])),
        goal :: [Atomic]
      }
  deriving (Eq)

setToList :: ConstraintSet -> [Atomic]
setToList (ConstraintSet ds is g) =
  concat (concatMap HashMap.elems (concatMap GHC.nameEnvElts (IntMap.elems ds)))
    ++ concat (concatMap HashMap.elems (concatMap GHC.nameEnvElts (IntMap.elems is)))
    ++ g

listToSet :: [Atomic] -> ConstraintSet
listToSet = foldr insert empty

instance Semigroup ConstraintSet where
  cs <> ds = fold (flip insert) ds cs

instance Monoid ConstraintSet where
  mempty = empty

instance GHC.Outputable ConstraintSet where
  ppr = fold (flip $ (GHC.$$) . GHC.ppr) GHC.empty

instance Binary ConstraintSet where
  put_ bh = put_ bh . setToList
    -- do
    --   put_ bh (IntMap.toList $ fmap GHC.nameEnvElts $ fmap (fmap HashMap.toList) (definite cs))
    --   put_ bh (IntMap.toList $ fmap GHC.nameEnvElts $ fmap (fmap HashMap.toList) (indefinite cs))
    --   put_ bh (goal cs)

  get bh = listToSet <$> get bh
    -- do
    --   df <- fmap (fmap HashMap.fromList) <$> (fmap GHC.mkNameEnv <$> (IntMap.fromList <$> Binary.get bh))
    --   nf <- fmap (fmap HashMap.fromList) <$> (fmap GHC.mkNameEnv <$> (IntMap.fromList <$> Binary.get bh))
    --   gl <- Binary.get bh
    --   return (ConstraintSet df nf gl)

instance Refined ConstraintSet where
  domain cs =
    foldMap (foldMapUFM (foldMap (foldMap domain))) (definite cs)
      <> foldMap (foldMapUFM (foldMap (foldMap domain))) (indefinite cs)
      <> foldMap domain (goal cs)
    where
      foldMapUFM f u =
        GHC.foldUFM (\a b -> f a <> b) mempty u

  rename x y cs =
    fold (\ds a -> unsafeInsert (rename x y a) ds) empty cs

empty :: ConstraintSet
empty =
  ConstraintSet
    { definite = mempty,
      indefinite = mempty,
      goal = []
    }

fold :: (b -> Atomic -> b) -> b -> ConstraintSet -> b
fold f z0 cs = z3
  where
    foldlUFM f b = IntMap.foldl' f b . GHC.ufmToIntMap
    !z1 = IntMap.foldl' (foldlUFM (HashMap.foldl' (List.foldl' f))) z0 (definite cs)
    !z2 = IntMap.foldl' (foldlUFM (HashMap.foldl' (List.foldl' f))) z1 (indefinite cs)
    !z3 = List.foldl' f z2 (goal cs)

-- | When `cs` is a constraint set, `size cs` is the number of constraints in it.
size :: ConstraintSet -> Int
size = fold (\sz _ -> 1 + sz) 0

mapAction :: Monad m => (Atomic -> m ()) -> ConstraintSet -> m ()
mapAction f cs = fold (\b a -> b >> f a) (return ()) cs

unsafeInsert :: Atomic -> ConstraintSet -> ConstraintSet
unsafeInsert a cs =
  case (left a, right a) of
    (Dom (Inj x xd), Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (definite cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] (x, xd) hm
       in cs {definite = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert (x, xd) (a : as) hm)) (definite cs)}
    (Con k _, Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (indefinite cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] k hm
       in cs {indefinite = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert k (a : as) hm)) (indefinite cs)}
    (_, Set _ _) -> cs {goal = a : goal cs}
    (_, _) -> cs

insert' :: Atomic -> ConstraintSet -> Maybe ConstraintSet
insert' a cs | not (tautology a) =
  case (left a, right a) of
    (Dom (Inj x xd), Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (definite cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] (x, xd) hm
       in fmap (\as' -> cs {definite = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert (x, xd) as' hm)) (definite cs)}) (maintain as)
    (Con k _, Dom (Inj y yd)) ->
      let ne = IntMap.findWithDefault mempty y (indefinite cs)
          hm = GHC.lookupWithDefaultUFM ne mempty yd
          as = HashMap.findWithDefault [] k hm
       in fmap (\as' -> cs {indefinite = IntMap.insert y (GHC.addToUFM ne yd (HashMap.insert k as' hm)) (indefinite cs)}) (maintain as)
    (_, Set _ _) ->
      fmap (\as' -> cs {goal = as'}) (maintain (goal cs))
    (_, _) -> Nothing -- Ignore constraints concerning base types
  where
    maintain ds =
      if any (a `impliedBy`) ds then Nothing else Just (a : filter (not . (`impliedBy` a)) ds)
insert' _ _ = Nothing

-- Add an atomic constriant to the set
-- ensuring to maintain the invariant
insert :: Atomic -> ConstraintSet -> ConstraintSet
insert a cs = Maybe.fromMaybe cs (insert' a cs)

-- Add a guard to every constraint
guardWith :: Guard -> ConstraintSet -> ConstraintSet
guardWith g cs =
  cs
    { definite = IntMap.map (GHC.mapUFM (HashMap.map (List.map go))) (definite cs),
      indefinite = IntMap.map (GHC.mapUFM (HashMap.map (List.map go))) (indefinite cs),
      goal = map go (goal cs)
    }
  where
    go a = a {guard = g <> guard a}

saturate :: IS.IntSet -> ConstraintSet -> ConstraintSet
saturate iface cs =
  if size ds <= size cs then ds else cs
  where
    dom = domain cs IS.\\ iface
    ds = State.execState (mapM_ saturateI $ IS.toList dom) cs

saturateI :: Int -> State ConstraintSet ()
saturateI i =
  do
    cs <- State.get -- dom is the domain of ds
    let df = IntMap.lookup i $ definite cs
    let nf = IntMap.lookup i $ indefinite cs
    let rs = cs {definite = IntMap.delete i (definite cs), indefinite = IntMap.delete i (indefinite cs)}
    let is = empty {definite = maybe mempty (IntMap.singleton i) df, indefinite = maybe mempty (IntMap.singleton i) nf}
    let filterRec1 =
          GHC.filterUFM (not . null) . fmap (HashMap.filter (not . null)) . fmap (fmap $ List.filter (\a -> not $ IS.member i $ domain (left a) <> domain (guard a)))
    let filterRec2 =
          GHC.filterUFM (not . null) . fmap (HashMap.filter (not . null)) . fmap (fmap $ List.filter (\a -> not $ IS.member i $ domain (left a) <> domain (guard a)))
    let ss = fixI (IS.singleton i) is is
    -- Remove any recursive clauses since saturation completed
    let ls = ss {definite = IntMap.adjust filterRec1 i (definite ss), indefinite = IntMap.adjust filterRec2 i (indefinite ss)}
    let ds = fst $ RWS.execRWS (saturateF (IS.singleton i) ls rs) mempty mempty
    let ds' = if debugging then trace ("[TRACE] SaturateI (#lhs: " ++ show (size ls) ++ ") (#rhs: " ++ show (size rs) ++ ") (#resolvants:" ++ show (size ds) ++ ")") ds else ds
    State.put ds'

fixI :: IS.IntSet -> ConstraintSet -> ConstraintSet -> ConstraintSet
fixI dom ls rs =
  case RWS.execRWS (saturateF dom ls rs) rs mempty of
    (!cs', Any True) -> fixI dom ls cs' -- New constraint have been found, i.e. not a fixedpoint
    (!cs', Any False) -> cs'

-- One step consequence operator for saturation rules concerning a particular refinement variable
saturateF :: IS.IntSet -> ConstraintSet -> ConstraintSet -> RWS ConstraintSet Any ConstraintSet ()
saturateF dom ls rs =
  mapAction resolveWith rs
  where
    addResolvant r = do
      es <- RWS.ask
      ds <- RWS.get
      case insert' r ds of
        Just ds' ->
          do
            RWS.put ds'
            case insert' r es of
              Nothing -> return ()
              Just _ -> RWS.tell (Any True)
        Nothing -> return ()
    resolveWith c = do
      let rss = resolve' dom ls c
      mapM_ addResolvant rss
