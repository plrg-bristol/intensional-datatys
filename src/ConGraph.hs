{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

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
import Data.Hashable
import qualified Data.Map as M
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
                             | (_, m) <- M.toList cg,
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
    Just cs -> Just $ ConGraph $ M.alter (\m -> Just $ foldr (\(kl, kr) -> insertBin kl kr top) (fromMaybe M.empty m) cs) d cg

-- Insert an edge into a bin
insertBin :: K L -> K R -> GuardSet -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
insertBin n m e = M.alter go n
  where
    go (Just b) = Just $ M.insertWith (|||) m e b
    go Nothing  = Just $ M.singleton m e

-- Guard a constraint graph by a set of possible guards
guardWith :: S.Set Name -> Int -> Name -> ConGraph -> ConGraph
guardWith ks x d (ConGraph cg) = ConGraph $ M.map (M.map (M.map (dom ks x d &&&))) cg

-- Combine two constraint graphs
union :: ConGraph -> ConGraph -> ConGraph
union (ConGraph x) (ConGraph y) = ConGraph $ M.unionWith (M.unionWith (M.unionWith (|||))) x y

-- Restrict a constraint graph to it's interface and check satisfiability
restrict :: S.Set Int -> ConGraph -> Either (K L, K R) ConGraph
restrict interface cg = runST $ runExceptT $ do
  mcg <- lift $ thaw cg
  trans inner mcg
  weaken inner mcg
  lift $ freeze mcg
  where
    inner = S.fromList (freevs cg) S.\\ interface

-- Default capacity
cap :: Int
cap = 16

-- A mutable constraing graph
newtype ConGraphM s = ConGraphM (M.Map Name (SubGraph s))

-- A disjoint graph for one datatype
data SubGraph s = SubGraph {
  edges :: STArray s (Int, Int) (M.Map (K L) (M.Map (K R) GuardSet)),
  left  :: STRef s (S.Set Int), -- Nodes
  right :: STRef s (S.Set Int)
}

-- Convert between mutable and unmutable graphs
freeze :: ConGraphM s -> ST s ConGraph
freeze (ConGraphM cg) = ConGraph <$> mapM freezeSub cg

freezeSub :: SubGraph s -> ST s (M.Map (K L) (M.Map (K R) GuardSet))
freezeSub g = do
  acc <- newSTRef M.empty
  forM_ (range ((0, 0), (cap, cap))) $ \ij -> do
    ebin <- readArray (edges g) ij
    curr <- readSTRef acc
    writeSTRef acc $ M.foldrWithKey (\n to curr' -> M.foldrWithKey (insertBin n) curr' to) curr ebin
  readSTRef acc

thaw :: ConGraph -> ST s (ConGraphM s)
thaw (ConGraph cg) = ConGraphM <$> mapM thawSub cg

thawSub :: M.Map (K L) (M.Map (K R) GuardSet) -> ST s (SubGraph s)
thawSub m = do
  edges <- newArray ((0, 0), (cap, cap)) M.empty
  left  <- newSTRef S.empty
  right <- newSTRef S.empty
  let g = SubGraph edges left right
  M.foldrWithKey (\n to a -> M.foldrWithKey (\m e a' -> a' >> insertAtomicM n m e g) a to) (return ()) m
  return g

-- Insert a new edge into a mutable graph
insertAtomicM :: K L -> K R -> GuardSet -> SubGraph s -> ST s ()
insertAtomicM n m e g = do
  let i = hash n `mod` cap
  let j = hash m `mod` cap
  ebin <- readArray (edges g) (i, j)
  writeArray (edges g) (i, j) (insertBin n m e ebin)
  modifySTRef (left g) (S.insert i)
  modifySTRef (right g) (S.insert j)

-- Add transitive edges through nodes in xs
trans :: S.Set Int -> ConGraphM s -> ExceptT (K L, K R) (ST s) ()
trans xs (ConGraphM m) = mapM_ (forM_ xs . transX) m

transX :: SubGraph s -> Int -> ExceptT (K L, K R) (ST s) ()
transX sg x = do
  is <- lift $ readSTRef (left sg)
  js <- lift $ readSTRef (right sg)
  forM_ is (\i ->
    forM_ js (\j -> do
      ik_bin <- lift $ readArray (edges sg) (i, hash (Dom x) `mod` cap)
      kj_bin <- lift $ readArray (edges sg) (hash (Dom x) `mod` cap, j)
      case M.lookup (Dom x) kj_bin of
        Nothing        -> return ()
        Just kj_guards ->
          M.foldrWithKey (\n n_to q -> do
            case M.lookup (Dom x) n_to of
              Nothing -> q
              Just nkg ->
                M.foldrWithKey (\m kmg q' -> do
                  let new_guard = nkg &&& kmg
                  if new_guard == bot
                    then q'
                    else
                      if safe n m
                        then do
                          lift $ insertAtomicM n m (nkg &&& kmg) sg
                          q'
                        else
                          throwError (n, m)
                  ) q kj_guards
            ) (return ()) ik_bin
      )
    )

-- Retrieve the predecessors of a node
preds :: K R -> SubGraph s -> ST s (M.Map (K L) GuardSet)
preds m g = do
  let j = hash m `mod` cap
  foldM (\k i -> do
    ebin <- readArray (edges g) (i, j)
    return $ M.union (M.map (fromMaybe bot . M.lookup m) ebin) k
    ) M.empty $ range (0, cap)

-- Update guards with preds of xs
weaken :: S.Set Int -> ConGraphM s -> ExceptT (K L, K R) (ST s) ()
weaken xs (ConGraphM cg) = mapM_ weakenX xs
  where
    weakenX x = do
      let j = hash (Dom x) `mod` cap
      preds <- M.foldrWithKey (\d sg macc -> do
        is <- lift $ readSTRef (left sg)
        acc <- macc
        p <- foldM (\acc' i -> do
          ebin <- lift $ readArray (edges sg) (i, j)
          let go (Dom y) g | y `elem` xs = return Nothing
                            | otherwise   = do
                              pp <- lift $ preds (Dom y) sg
                              if M.null pp
                                then return $ Just (d, g)
                                else return $ Nothing
              go (Con c l) g = return $ Just (d, g)
          preds_x <- M.traverseMaybeWithKey go $ M.map (fromMaybe bot . M.lookup (Dom x)) ebin
          return (M.union preds_x acc')
          ) acc is

        lift $ removeNode x sg
        return p
        ) (return M.empty) cg

      M.foldrWithKey (\n (d, g) q -> do
        forM cg $ lift . mapGuards (\g' -> filterGuards xs g' ||| replace x d n g' &&& g)
        -- check safety
        q
        ) (return ()) preds

-- map array in place
mapGuards :: (GuardSet -> GuardSet) -> SubGraph s -> ST s ()
mapGuards f sg = do
  is <- readSTRef (left sg)
  js <- readSTRef (right sg)
  forM_ is $ \i ->
    forM_ js $ \j -> do
      x <- readArray (edges sg) (i, j)
      writeArray (edges sg) (i, j) (M.map (M.map f) x)

-- Remove a node
-- TODO: Check bin isn't empty
removeNode :: Int -> SubGraph s -> ST s ()
removeNode n sg = do
  is <- readSTRef (left sg)
  js <- readSTRef (right sg)
  forM_ is $ \i ->
    forM_ js $ \j -> do
      x <- readArray (edges sg) (i, j)
      writeArray (edges sg) (i, j) (M.map (M.delete (Dom n)) $ M.delete (Dom n) x)
