{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiWayIf #-}

module ConGraph (
  ConGraph(..),
  empty,
  insert,
  union,
  getPreds,
  getSuccs,
  guardWith,
  restrict,
) where

import Prelude hiding ((<>))
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
import Outputable hiding (empty, isEmpty)

import Types
import Constraints

-- A collection of disjoint graphs for each datatype
-- Nodes are constructor sets or refinement variables
-- Edges are labelled by possible guards.
newtype ConGraph = ConGraph (M.Map (DataType Name) (M.Map (K L) (M.Map (K R) GuardSet)))
  deriving Eq

instance (Refined k, Ord k, Refined a) => Refined (M.Map k a) where
  freevs m =
    let keydom = foldr (L.union . freevs) [] $ M.keysSet m
    in  foldr (L.union . freevs) keydom m
  rename x y = M.mapKeys (rename x y) . M.map (rename x y)

instance Refined ConGraph where
  freevs (ConGraph cg)    = freevs cg
  rename x y (ConGraph m) = ConGraph $ rename x y m

instance Outputable ConGraph where
  ppr (ConGraph cg) = vcat [ ppr g <+> case k1 of {Dom _ -> ppr d <> parens (ppr k1); _ -> ppr k1} <+> arrowt <+> case k2 of {Dom _ -> ppr d <> parens (ppr k2); _ -> ppr k2}
                           | (d, m)   <- M.toList cg,
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
insert :: K l -> K r -> DataType Name -> ConGraph -> Maybe ConGraph
insert k1 k2 d (ConGraph cg) =
  case toAtomic k1 k2 of
    Nothing -> Nothing
    Just cs -> Just $ ConGraph $ M.alter (Just . overwriteBin cs . fromMaybe M.empty) d cg

-- Overwrite bin, i.e. insert with top
overwriteBin :: [(K L, K R)] -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
overwriteBin cs m = L.foldl' (\k (kl, kr) -> insertBin kl kr top k) m cs

-- Guard a constraint graph by a set of possible guards
guardWith :: S.Set Name -> Int -> DataType Name -> ConGraph -> ConGraph
guardWith ks x d (ConGraph cg) = ConGraph $ M.map (M.map (M.map (dom ks x d &&&))) cg

-- Combine two constraint graphs
union :: ConGraph -> ConGraph -> ConGraph
union (ConGraph x) (ConGraph y) = ConGraph $ M.unionWith (M.unionWith (M.unionWith (|||))) x y

-- Get predecessors of a node
getPreds :: Int -> DataType Name -> ConGraph -> M.Map (K L) GuardSet
getPreds x d (ConGraph cg) =
  case M.lookup d cg of
    Nothing -> M.empty
    Just m  -> M.mapMaybe (M.lookup (Dom x)) m

getSuccs :: Int -> DataType Name -> ConGraph -> M.Map (K R) GuardSet
getSuccs x d (ConGraph cg) = fromMaybe (M.empty) (M.lookup d cg >>= M.lookup (Dom x))

-- Restrict a constraint graph to it's interface and check satisfiability
restrict :: [Int] -> ConGraph -> Either (K L, K R) ConGraph
restrict interface cg = runST $ runExceptT $ do
  mcg <- lift $ thaw cg
  trans inner mcg
  preds <- lift $ weaken inner mcg
  -- Check sat
  freeze inner preds mcg
  where
    inner = freevs cg L.\\ interface

-- A mutable constraint graph
newtype ConGraphM s = ConGraphM (M.Map (DataType Name) (SubGraph s))

-- A disjoint graph for one datatype
data SubGraph s = SubGraph {
  edges :: STArray s (Int, Int) (M.Map (K L) (M.Map (K R) GuardSet)),
  left  :: STRef s [Int], -- Inhabited indices
  right :: STRef s [Int]
}

-- Default capacity
cap :: Int
cap = 17

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
  _ <- M.traverseWithKey (\n -> M.traverseWithKey (\m e -> insertAtomicM n m e msub)) sub
  return msub

-- Make immutable copy of mutable constraint graph
freeze :: [Int] -> M.Map Int (M.Map (DataType Name) (M.Map (K L) GuardSet)) -> ConGraphM s -> ExceptT (K L, K R) (ST s) ConGraph
freeze xs preds (ConGraphM cg) = ConGraph <$> mapM freezeSub cg
  where
    freezeSub :: SubGraph s -> ExceptT (K L, K R) (ST s) (M.Map (K L) (M.Map (K R) GuardSet))
    freezeSub msub = do
      sub <- lift $ newSTRef M.empty
      is  <- lift $ readSTRef (left msub)
      js  <- lift $ readSTRef (right msub)
      forM_ is $ \i ->
        forM_ js $ \j -> do
          ebin <- lift $ readArray (edges msub) (i, j)
          sub' <- M.foldlWithKey' (\ma n n_to -> ma >>= \a -> M.foldlWithKey' (\ma' m g -> ma' >>= \a' -> freezeInsert n m g a') (return a) n_to) (lift $ readSTRef sub) ebin
          lift $ writeSTRef sub sub'
      lift $ readSTRef sub

    freezeInsert :: K L -> K R -> GuardSet -> M.Map (K L) (M.Map (K R) GuardSet) -> ExceptT (K L, K R) (ST s) (M.Map (K L) (M.Map (K R) GuardSet))
    freezeInsert n m g s =
      case n of
        Dom y | y `elem` xs -> return s
        _ ->
          case m of
            Dom y | y `elem` xs -> return s
            _ -> do
              let new_guard = applyPreds preds g
              if isEmpty new_guard
                then return s
                else case toAtomic n m of
                  Nothing  -> throwError (n, m)
                  Just []  -> return s
                  Just [_] -> return $ insertBin n m new_guard s


-- Insert a new edge into a mutable graph
insertAtomicM :: K L -> K R -> GuardSet -> SubGraph s -> ST s ()
insertAtomicM n m e g = do
  let i = getIndex n
  let j = getIndex m
  ebin <- readArray (edges g) (i, j)
  writeArray (edges g) (i, j) (insertBin n m e ebin)
  modifySTRef (left g) (L.insert i)
  modifySTRef (right g) (L.insert j)

-- Insert an edge into a bin
insertBin :: K L -> K R -> GuardSet -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
insertBin n m e gs
  | isEmpty e = gs
  | otherwise = M.alter go n gs
  where
    go (Just b) = Just $ M.insertWith (|||) m e b
    go Nothing  = Just $ M.singleton m e

-- Add transitive edges through nodes in xs
trans :: [Int] -> ConGraphM s -> ExceptT (K L, K R) (ST s) ()
trans xs (ConGraphM m) = mapM_ (forM_ xs . transX) m
  where
    transX :: SubGraph s -> Int -> ExceptT (K L, K R) (ST s) ()
    transX sg x = do
      js <- lift $ readSTRef (right sg)
      forM_ js (\j -> do
        kj_bin <- lift $ readArray (edges sg) (getIndex $ Dom x, j)
        forM_ (M.lookup (Dom x) kj_bin) $ \kj_guards ->
          M.traverseWithKey (\m kmg -> do
            is <- lift $ readSTRef (left sg)
            forM_ is (\i -> do
              ik_bin <- lift $ readArray (edges sg) (i, getIndex $ Dom x)
              M.traverseWithKey (\n -> mapM_ (\nkg -> do

                -- Add new edge from n to m through (Dom x)
                let new_guard = nkg &&& kmg
                ijbin <- lift $ readArray (edges sg) (i, j)
                lift $ writeArray (edges sg) (i, j) (insertBin n m new_guard ijbin)

                ) . M.lookup (Dom x)) ik_bin
              )
            ) kj_guards
        )

-- Weaken guards containing intermediate variables
weaken :: [Int] -> ConGraphM s -> ST s (M.Map Int (M.Map (DataType Name) (M.Map (K L) GuardSet)))
weaken xs (ConGraphM cg) = foldM (\ps x -> (\xps -> updatePreds x xps ps) <$> weakenX x) M.empty xs
  where
    -- Predecesor of x
    weakenX x =
      M.traverseMaybeWithKey (\_ sg -> do
        -- Predecessors of X(d)
        is <- readSTRef (left sg)
        let j = getIndex (Dom x)
        p_map <- foldM (\xd_preds i -> do
          ebin <- readArray (edges sg) (i, j)
          -- Predecessors of X(d) from bins (i, j)
          return $ M.foldlWithKey' (\xd_preds n n_to ->
            case M.lookup (Dom x) n_to of
              Nothing -> xd_preds -- n is not a predecessor
              Just g  ->
                case n of
                  Dom y | y `elem` xs -> xd_preds -- Don't weaken to another intermediate node
                  _                   -> M.insert n g xd_preds
            ) xd_preds ebin
          ) M.empty is
        removeNode x sg
        if M.null p_map
          then return Nothing
          else return $ Just p_map
        ) cg

-- Apply existing preds and then insert
updatePreds :: Int -> M.Map (DataType Name) (M.Map (K L) GuardSet) -> M.Map Int (M.Map (DataType Name) (M.Map (K L) GuardSet)) -> M.Map Int (M.Map (DataType Name) (M.Map (K L) GuardSet))
updatePreds x x_preds preds =
  let x_preds' = M.map (M.map (applyPreds preds)) x_preds
  in M.insert x x_preds' preds

-- Lazily remove a node, i.e. don't remove index
removeNode :: Int -> SubGraph s -> ST s ()
removeNode n sg = do
  is <- readSTRef (left sg)
  forM_ is $ \i -> do
    x <- readArray (edges sg) (getIndex (Dom n), i)
    writeArray (edges sg) (getIndex $ Dom n, i) (M.map (M.delete (Dom n)) $ M.delete (Dom n) x)

  js <- readSTRef (right sg)
  forM_ js $ \j -> do
    y <- readArray (edges sg) (j, getIndex (Dom n))
    writeArray (edges sg) (j, getIndex $ Dom n) (M.map (M.delete (Dom n)) $ M.delete (Dom n) y)
