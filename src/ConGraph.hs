{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE BangPatterns #-}

module ConGraph (
  ConGraph,
  empty,
  insert,
  union,
  guardWith,
  restrict,
) where

import Control.Monad.ST
import Control.Monad.Except

import Data.Maybe
import Data.STRef
import Data.Array.ST hiding (freeze, thaw)
import Data.Foldable hiding (toList)
import Data.Hashable
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.List as L

import Name
import Binary
import Outputable hiding (empty)

import Types
import Constraints

-- A collection of disjoint graphs for each datatype
-- Nodes are constructor sets or refinement variables
-- Edges are labelled by possible guards.
newtype ConGraph = ConGraph (M.Map Name (M.Map (K L) (M.Map (K R) GuardSet)))
  deriving Eq

instance (Refined k, Ord k, Refined a) => Refined (M.Map k a) where
  freevs m =
    let keydom = foldr (L.union . freevs) [] $ M.keysSet m
    in  foldr (L.union . freevs) keydom m
  rename x y = M.mapKeys (rename x y) . M.map (rename x y)

instance Refined ConGraph where
  freevs (ConGraph cg)    = foldr (L.union . freevs) [] cg
  rename x y (ConGraph m) = ConGraph $ M.map (rename x y) m

instance Outputable ConGraph where
  ppr (ConGraph cg) = vcat [ ppr g <+> ppr k1 <+> arrowt <+> ppr k2
                             | (_, m)   <- M.toList cg,
                               (k1, m') <- M.toList m,
                               (k2, gs) <- M.toList m',
                               g <- toList gs]

instance Binary ConGraph where
  put_ bh (ConGraph cg) = put_ bh [ (n, [ (k1, M.toList m') | (k1, m') <- M.toList m]) | (n, m) <- M.toList cg]
  get bh = do
    nl <- get bh
    let nl' = [(n, M.fromList [(k, M.fromList m') | (k, m') <- l]) | (n, l) <- nl]
    return (ConGraph $ M.fromList nl')

-- An empty set
empty :: ConGraph
empty = ConGraph M.empty

-- Insert a non-atomic constraint with trivial guard
insert :: K l -> K r -> Name -> ConGraph -> Maybe ConGraph
insert k1 k2 d (ConGraph cg) =
  case toAtomic k1 k2 of
    Nothing -> Nothing
    Just cs -> Just $ ConGraph $ M.alter (Just . overwriteBin cs . fromMaybe M.empty) d cg

-- Overwrite bin, i.e. insert with top
overwriteBin :: [(K L, K R)] -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
overwriteBin cs m = L.foldl' (\k (kl, kr) -> insertBin kl kr top k) m cs

-- Guard a constraint graph by a set of possible guards
guardWith :: S.Set Name -> Int -> Name -> ConGraph -> ConGraph
guardWith ks x d (ConGraph cg) = ConGraph $ fmap (fmap (fmap (dom ks x d &&&))) cg

-- Combine two constraint graphs
union :: ConGraph -> ConGraph -> ConGraph
union (ConGraph x) (ConGraph y) = ConGraph $ M.unionWith (M.unionWith (M.unionWith (|||))) x y

-- Restrict a constraint graph to it's interface and check satisfiability
restrict :: [Int] -> ConGraph -> Either (K L, K R) ConGraph
restrict interface cg = runST $ runExceptT $ do
  mcg <- lift $ thaw cg
  trans inner mcg
  weaken inner mcg
  -- Check sat
  lift $ freeze mcg
  where
    inner = freevs cg L.\\ interface

-- A mutable constraint graph
newtype ConGraphM s = ConGraphM (M.Map Name (SubGraph s))

-- A disjoint graph for one datatype
data SubGraph s = SubGraph {
  edges :: STArray s (Int, Int) (M.Map (K L) (M.Map (K R) GuardSet)),
  left  :: STRef s [Int], -- Inhabited indices
  right :: STRef s [Int]
}

-- Default capacity
cap :: Int
cap = 16

getIndex :: K a -> Int
getIndex k = mod (hash k) 16

-- Make mutable copy of immutable constraint graph
thaw :: ConGraph -> ST s (ConGraphM s)
thaw (ConGraph cg) = ConGraphM <$> mapM thawSub cg

thawSub :: M.Map (K L) (M.Map (K R) GuardSet) -> ST s (SubGraph s)
thawSub sub = do
  e <- newArray ((0, 0), (cap, cap)) M.empty
  l <- newSTRef []
  r <- newSTRef []
  let msub = SubGraph e l r
  traverseWithKey_' (\n -> traverseWithKey_' (\m e -> insertAtomicM n m e msub)) sub
  return msub

-- Make immutable copy of mutable constraint graph
freeze :: ConGraphM s -> ST s ConGraph
freeze (ConGraphM cg) = ConGraph <$> mapM freezeSub cg

freezeSub :: SubGraph s -> ST s (M.Map (K L) (M.Map (K R) GuardSet))
freezeSub msub = do
  sub <- newSTRef M.empty
  is  <- readSTRef (left msub)
  js  <- readSTRef (right msub)
  forM_' is $ \i ->
    forM_' js $ \j -> do
      ebin <- readArray (edges msub) (i, j)
      modifySTRef sub (\s -> M.foldlWithKey' (\s' n n_to -> M.foldlWithKey' (\s'' m g -> insertBin n m g s'') s' n_to) s ebin)
  readSTRef sub

-- Insert a new edge into a mutable graph
insertAtomicM :: K L -> K R -> GuardSet -> SubGraph s -> ST s ()
insertAtomicM !n !m !e !g = do
  let !i = getIndex n
  let !j = getIndex m
  !ebin <- readArray (edges g) (i, j)
  !() <- writeArray (edges g) (i, j) (insertBin n m e ebin)
  !() <- modifySTRef (left g) (L.insert i)
  modifySTRef (right g) (L.insert j)

-- Insert an edge into a bin
insertBin :: K L -> K R -> GuardSet -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
insertBin n m e = M.alter go n
  where
    go (Just b) = Just $ M.insertWith (|||) m e b
    go Nothing  = Just $ M.singleton m e

-- Add transitive edges through nodes in xs
trans :: [Int] -> ConGraphM s -> ExceptT (K L, K R) (ST s) ()
trans xs (ConGraphM m) = mapM_ (forM_' xs . transX) m

transX :: SubGraph s -> Int -> ExceptT (K L, K R) (ST s) ()
transX sg x = do
  is <- lift $ readSTRef (left sg)
  js <- lift $ readSTRef (right sg)
  forM_' is (\i ->
    forM_' js (\j -> do
      ik_bin <- lift $ readArray (edges sg) (i, getIndex k)
      kj_bin <- lift $ readArray (edges sg) (getIndex k, j)
      -- Consider every path from these bins
      forM_' (M.lookup k kj_bin) $ \kj_guards ->
        traverseWithKey_' (\n -> mapM_ (\nkg ->
          traverseWithKey_' (\m kmg -> do
            -- Add new edge if safe
            let new_guard = nkg &&& kmg
            if | new_guard == bot -> return ()
               | safe n m         -> lift $ insertAtomicM n m (nkg &&& kmg) sg
               | otherwise        -> throwError (n, m)
            ) kj_guards
          ) . M.lookup k
        ) ik_bin
      )
    )
  where
    -- The transitive node
    k :: K a
    k = Dom x

-- Weaken guards containing intermediate variables
weaken :: [Int] -> ConGraphM s -> ExceptT (K L, K R) (ST s) ()
weaken xs (ConGraphM cg) = mapM_ weakenX xs
  where
    -- Replace x with it's predecesors in guards
    weakenX x = () <$ do
      -- Gather all predecesor of x
      preds <- traverse (\sg -> do
        is <- lift $ readSTRef (left sg)
        p <- forM is $ \i -> do
          let j = getIndex (Dom x)
          ebin <- lift $ readArray (edges sg) (i, j)
          M.traverseMaybeWithKey (\p p_to ->
            case M.lookup (Dom x) p_to of
              Nothing -> return Nothing -- p is not a predecessor
              Just g  ->
                case p of
                  Dom y | y `elem` xs -> return Nothing -- Don't weaken to another intermediate node
                  _                   -> return $ Just g
            ) ebin

        lift $ removeNode x sg
        return p
        ) cg

      traverseWithKey_' (\d -> mapM_ (traverseWithKey_' (\p -> forM_' cg . replaceSubGraph x d p))) preds

-- Replace all guards in a subgraph
replaceSubGraph :: Int -> Name -> K L -> GuardSet -> SubGraph s -> ExceptT (K L, K R) (ST s) ()
replaceSubGraph x d n g sg = do
  is <- lift $ readSTRef (left sg)
  js <- lift $ readSTRef (right sg)
  forM_' is $ \i ->
    forM_' js $ \j -> do
      bin <- lift $ readArray (edges sg) (i, j)
      bin' <- replaceBin x d n g bin
      lift $ writeArray (edges sg) (i, j) bin'

-- Replace all guards in abin
replaceBin :: Int -> Name -> K L -> GuardSet -> M.Map (K L) (M.Map (K R) GuardSet) -> ExceptT (K L, K R) (ST s) (M.Map (K L) (M.Map (K R) GuardSet))
replaceBin x d n g = M.traverseWithKey (\r -> M.traverseWithKey (\l rlg -> do
  let rlg' = remove x rlg ||| replace x d n rlg &&& g
  if safe r l || rlg' == bot
    then return rlg'
    else throwError (n, l)
  ))

-- Lazily remove a node, i.e. don't remove index
removeNode :: Int -> SubGraph s -> ST s ()
removeNode n sg = do
  is <- readSTRef (left sg)
  js <- readSTRef (right sg)
  forM_' is $ \i -> do
    x <- readArray (edges sg) (getIndex (Dom n), i)
    writeArray (edges sg) (getIndex $ Dom n, i) (M.map (M.delete (Dom n)) $ M.delete (Dom n) x)

    y <- readArray (edges sg) (i, getIndex (Dom n))
    writeArray (edges sg) (i, getIndex $ Dom n) (M.map (M.delete (Dom n)) $ M.delete (Dom n) y)

-- Strict forM_
forM_' :: (Monad m, Foldable f) => f a -> (a -> m ()) -> m ()
forM_' !xs !f = foldl' (\b a -> b >> f a) (return ()) xs

-- Strict traverseWithKey
traverseWithKey_' :: Monad m => (k -> a -> m ()) -> M.Map k a -> m ()
traverseWithKey_' !f !m = M.foldlWithKey' (\q k a -> q >> f k a) (return ()) m
