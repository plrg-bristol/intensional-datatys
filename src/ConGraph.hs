{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}

module ConGraph
  ( ConGraph,
    IfConGraph,
    ConGraphGen,
    empty,
    insert,
    union,
    unionUniq,
    guardWith,
    mergeLevel,
    restrict,
  )
where

import Binary
import Constraints
import Control.Monad
import Control.Monad.Except
import Data.Bifunctor
import qualified Data.HashMap.Lazy as H
import Data.Hashable
import qualified Data.List as L
import Data.Maybe
import Data.Functor.Identity
import DataTypes
import GhcPlugins hiding (L, empty, isEmpty, singleton)
import Guards
import Types
import Prelude hiding ((<>))

-- A constraint graph for a fixed datatype
type SubGraph s = H.HashMap (K 'L) (H.HashMap (K 'R) (GuardSet s))

-- Map keys
mapKeys :: (Hashable k', Eq k') => (k -> k') -> H.HashMap k v -> H.HashMap k' v
mapKeys f = H.fromList . fmap (first f) . H.toList

traverseMaybeWithKey :: Applicative f => (k -> v -> f (Maybe v)) -> H.HashMap k v -> f (H.HashMap k v)
traverseMaybeWithKey f m = H.mapMaybe id <$> H.traverseWithKey f m

-- Merger maps with a monad function
unionWithM :: (Hashable a, Eq a, Monad m) => (b -> b -> m b) -> H.HashMap a b -> H.HashMap a b -> m (H.HashMap a b)
unionWithM f x y = sequence $ H.unionWith (\x y -> x >>= \a -> y >>= f a) (H.map return x) (H.map return y)

-- Insert several atomic constraints with the same guard
insertSub :: GsM state s m => K 'L -> K 'R -> GuardSet s -> SubGraph s -> m (SubGraph s)
insertSub kl kr g = H.alterF go kl
  where
    go (Just b) = Just <$> unionWithM (|||) (H.singleton kr g) b
    go Nothing = return (Just $ H.singleton kr g)

-- Insert several atomic constraints with the same lhs
insertMany :: GsM state s m => K 'L -> H.HashMap (K 'R) (GuardSet s) -> SubGraph s -> m (SubGraph s)
insertMany kl m = H.alterF go kl
  where
    go (Just m') = Just <$> unionWithM (|||) m m'
    go Nothing = return (Just m)

-- Combine subgraphs
unionSub :: GsM state s m => SubGraph s -> SubGraph s -> m (SubGraph s)
unionSub = unionWithM (unionWithM (|||))

-- Take the transitive closure of a subgraph
transSub :: GsM state s m => [RVar] -> SubGraph s -> m (SubGraph s)
transSub xs orig_graph = do
  -- explore spanning-tree from interface nodes
  (ns, g) <- foldM go ([], orig_graph) $ fmap Dom xs
  -- explore spanning-tree from source constructors
  snd <$> foldM go (ns, g) [Con k l | (Con k l) <- H.keys orig_graph]
  where
    go (ns, es) n =
      case H.lookup n orig_graph of
        Nothing -> return (ns, es)
        Just from_n
          | n `elem` ns -> return (ns, es)
          | otherwise ->
            H.foldrWithKey
              ( \m g state ->
                  case m of
                    Set _ _ -> state
                    Dom x -> do
                      s <- state
                      (ns', es') <- go s (Dom x)
                      case H.lookup (Dom x) es' of
                        Nothing -> return (ns', es')
                        Just from_d -> do
                          n_via_d <- mapM (||| g) from_d
                          g'' <- insertMany n n_via_d es'
                          return (ns', g'')
              )
              (return (n : ns, es))
              from_n

-- Collect the predecessors of intermediate nodes
predsSub :: [RVar] -> SubGraph s -> H.HashMap RVar (H.HashMap (K 'L) (GuardSet s))
predsSub xs orig_graph =
  H.fromList $
    fmap
      ( \x ->
          ( x,
            H.mapMaybeWithKey
              ( \n rs ->
                  case H.lookup (Dom x) rs of
                    Just p
                      | interface n -> Just p
                    _ -> Nothing
              )
              orig_graph
          )
      )
      xs
  where
    interface :: K 'L -> Bool
    interface Con {} = True
    interface (Dom x) = x `notElem` xs

-- A collection of disjoint subgraphs for each datatypes
-- Nodes are constructor sets or refinement variables
-- Edges are labelled by possible guards
type ConGraph s = ConGraphGen (GuardSet s)

type IfConGraph = ConGraphGen [[Guard]]

data ConGraphGen g
  = ConGraph
      { subgraphs :: H.HashMap (DataType Name) (H.HashMap (K 'L) (H.HashMap (K 'R) g)),
        _domain :: [RVar]
      }
  deriving (Eq, Functor, Foldable, Traversable)

instance Outputable IfConGraph where
  ppr cg =
    vcat
      [ ppr g <+> pprCon k1 d <+> arrowt <+> pprCon k2 d
        | (d, sg) <- H.toList $ subgraphs cg,
          (k1, to) <- H.toList sg,
          (k2, gs) <- H.toList to,
          g <- gs
      ]
    where
      pprCon k@(Dom _) d = ppr d <> parens (ppr k)
      pprCon k _ = ppr k

instance Binary IfConGraph where
  put_ bh (ConGraph cg d) = put_ bh [(n, [(k1, H.toList m') | (k1, m') <- H.toList m]) | (n, m) <- H.toList cg] >> put_ bh d
  get bh = do
    nl <- get bh
    d <- get bh
    let nl' = [(n, H.fromList [(k, H.fromList m') | (k, m') <- l]) | (n, l) <- nl]
    return (ConGraph (H.fromList nl') d)

instance (GsM state s m, Refined g m) => Refined (ConGraphGen g) m where
  domain = return . _domain

  rename x y (ConGraph cg d) = do
    cg' <-
      mapM
        ( fmap (mapKeys (runIdentity . rename x y))
            . mapM (fmap (mapKeys (runIdentity . rename x y)) . mapM (rename x y))
        )
        cg
    return (ConGraph cg' ((y : d) L.\\ [x]))

  renameAll xys (ConGraph cg d) = do
    cg' <-
      mapM
        ( fmap (mapKeys (runIdentity . renameAll xys))
            . mapM (fmap (mapKeys (runIdentity . renameAll xys)) . mapM (renameAll xys))
        )
        cg
    return (ConGraph cg' ((fmap snd xys ++ d) L.\\ fmap fst xys))

-- An empty constraint set
empty :: ConGraphGen g
empty = ConGraph H.empty []

-- Insert an atomic constraint
insert :: GsM state s m => K 'L -> K 'R -> GuardSet s -> DataType Name -> ConGraph s -> m (ConGraph s)
insert k1 k2 g dty (ConGraph cg d) = do
  cg' <- H.alterF (fmap Just . insertSub k1 k2 g . fromMaybe H.empty) dty cg
  dk1 <- domain k1
  dk2 <- domain k2
  dg <- domain g
  return (ConGraph cg' (dk1 `L.union` dk2 `L.union` dg `L.union` d))

-- Guard a constraint graph with by a set of possible guards
guardWith :: GsM state s m => GuardSet s -> ConGraph s -> m (ConGraph s)
guardWith g = mapM (&&& g)

-- Combine two constraint graphs
union :: GsM state s m => ConGraph s -> ConGraph s -> m (ConGraph s)
union (ConGraph x d) (ConGraph y d') = do
  xy <- unionWithM unionSub x y
  return (ConGraph xy (d `L.union` d'))

-- Combine two disjoint constraint graphs
unionUniq :: ConGraph s -> ConGraph s -> ConGraph s
unionUniq (ConGraph x d) (ConGraph y d') = ConGraph (H.unionWith (H.unionWith H.union) x y) (d `L.union` d')

-- Duplicate constraints between levels
mergeLevel :: GsM state s m => RVar -> RVar -> DataType Name -> DataType Name -> ConGraph s -> m (ConGraph s)
mergeLevel x y xd yd cg@(ConGraph sg _) = do
  -- Add each pred of x to the datatype y level
  cg' <-
    H.foldrWithKey
      (\xp g mcg -> mcg >>= insert xp (Dom x) g yd)
      (return cg)
      x_preds
  -- Add each succ of y to the x datatype level
  H.foldrWithKey
    (\ys g mcg -> mcg >>= insert (Dom y) ys g xd)
    (return cg')
    y_succs
  where
    x_preds = case H.lookup xd sg of
      Nothing -> H.empty
      Just m -> H.mapMaybe (H.lookup (Dom x)) m
    y_succs = fromMaybe H.empty (H.lookup yd sg >>= H.lookup (Dom y))

-- Restrict a constraint graph to it's interface and check satisfiability
restrict :: GsM state s m => [RVar] -> ConGraph s -> ExceptT (DataType Name, K 'L, K 'R) m (ConGraph s)
restrict interface (ConGraph cg cg_dom) = do
  cg' <- lift $ mapM (transSub interface) cg
  let preds = predsSub (cg_dom L.\\ interface) <$> cg'
  sgs <-
    H.traverseWithKey
      ( \dty ->
          traverseMaybeWithKey
            ( \l rs ->
                if irrelevantLeft l
                  then return Nothing
                  else 
                    Just
                      <$> traverseMaybeWithKey
                        ( \r g ->
                            if irrelevantRight l r
                              then return Nothing
                              else do
                                new_guard <- lift $ applyPreds preds g
                                e <- lift $ isEmpty new_guard
                                if safe l r || e
                                  then return $ Just new_guard
                                  else throwError (dty, l, r)
                        )
                        rs
            )
      )
      cg'
  return (ConGraph sgs interface)
  where
    irrelevantLeft (Dom x) = x `notElem` interface
    irrelevantLeft _ = False

    irrelevantRight (Dom x) (Dom y) = y `notElem` interface || x == y
    irrelevantRight _ (Dom y) = y `notElem` interface
    irrelevantRight (Con k _) (Set ks _) = elementOfUniqSet k ks
    irrelevantRight _ _ = False