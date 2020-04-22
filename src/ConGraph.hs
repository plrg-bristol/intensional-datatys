{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiWayIf #-}

module ConGraph
  ( ConGraph,
    empty,
    insert,
    union,
    getPreds,
    getSuccs,
    guardWith,
    guardDirect,
    restrict,
  )
where

import qualified Binary as B
import Constraints
import Control.Monad.Except
import Control.Monad.ST
import Control.Monad.State
import Data.Array.ST hiding (freeze, thaw)
import Data.Hashable
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Data.Maybe
import Data.STRef
import qualified Data.Set as S
import FastString
import Name
import Outputable hiding (empty, isEmpty)
import SrcLoc hiding (L)
import Types
import Prelude hiding ((<>), lookup)

-- A collection of disjoint graphs for each datatype
-- Nodes are constructor sets or refinement variables
-- Edges are labelled by possible guards.
-- ConGraphs should have a free variable map
newtype ConGraph = ConGraph (M.Map (DataType Name) (M.Map (K L) (M.Map (K R) GuardSet)))
  deriving (Eq)

instance (Refined k, Ord k, Refined a) => Refined (M.Map k a) where
  freevs m = foldr (L.union . freevs) (foldr (L.union . freevs) [] $ M.keysSet m) m
  rename x y = M.mapKeys (rename x y) . M.map (rename x y)

instance Refined ConGraph where
  freevs (ConGraph cg) = freevs cg
  rename x y (ConGraph m) = ConGraph $ rename x y m

instance Outputable ConGraph where
  ppr (ConGraph cg) =
    vcat
      [ ppr g <+> case k1 of { Dom _ -> ppr d <> parens (ppr k1); _ -> ppr k1 } <+> arrowt <+> case k2 of Dom _ -> ppr d <> parens (ppr k2); _ -> ppr k2
        | (d, m) <- M.toList cg,
          (k1, m') <- M.toList m,
          (k2, gs) <- M.toList m',
          g <- toList gs
      ]

instance B.Binary ConGraph where
  put_ bh (ConGraph cg) = B.put_ bh [(n, [(k1, M.toList m') | (k1, m') <- M.toList m]) | (n, m) <- M.toList cg]
  get bh = do
    nl <- B.get bh
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
overwriteBin cs m = foldr (\(kl, kr) k -> insertBin kl kr Top k) m cs

-- Insert an edge into a bin
insertBin :: K L -> K R -> GuardSet -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
insertBin n m e = M.alter go n
  where
    go (Just b) = Just $ M.insertWith (:||) m e b
    go Nothing = Just $ M.singleton m e

-- Guard a constraint graph by a set of possible guards
guardWith :: [Name] -> Int -> DataType Name -> ConGraph -> ConGraph
guardWith ks x = guardDirect . dom ks x

-- Guard a constraint graph with by a set of possible guards
guardDirect :: GuardSet -> ConGraph -> ConGraph
guardDirect g (ConGraph cg) = ConGraph $ M.map (M.map (M.map (g :&&))) cg

-- Combine two constraint graphs
union :: ConGraph -> ConGraph -> ConGraph
union (ConGraph x) (ConGraph y) = ConGraph $ M.unionWith (M.unionWith (M.unionWith (:||))) x y

-- Get predecessors of a node
getPreds :: Int -> DataType Name -> ConGraph -> M.Map (K L) GuardSet
getPreds x d (ConGraph cg) =
  case M.lookup d cg of
    Nothing -> M.empty
    Just m -> M.mapMaybe (M.lookup (Dom x)) m

getSuccs :: Int -> DataType Name -> ConGraph -> M.Map (K R) GuardSet
getSuccs x d (ConGraph cg) = fromMaybe M.empty (M.lookup d cg >>= M.lookup (Dom x))

transDisjoint :: [Int] -> ConGraph -> ConGraph
transDisjoint interface (ConGraph sgs) = ConGraph $ M.map go sgs
  where
    sources sg = fmap Dom interface ++ [Con k l | (Con k l) <- M.keys sg]
    go sg = trans (sources sg) sg

trans :: [K L] -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
trans vs graph = snd $ execState (mapM_ go vs) ([], graph)
  where
    go :: K L -> State ([K L], M.Map (K L) (M.Map (K R) GuardSet)) ()
    go v =
      case M.lookup v graph of
        Nothing -> return ()
        Just from_v -> do
          (seen, acc) <- get
          unless (v `elem` seen) $ do
            put (v : seen, acc)
            M.traverseWithKey
              ( \d g ->
                  case d of
                    Dom x -> do
                      go (Dom x)
                      (seen, acc) <- get
                      case M.lookup (Dom x) acc of
                        Nothing -> return ()
                        Just from_d ->
                          put (seen, M.insertWith (M.unionWith (:||)) v (M.map (:&& g) from_d) acc)
                    Set ks l -> do
                      (seen, acc) <- get
                      put (seen, M.insertWith (M.unionWith (:||)) v (M.singleton (Set ks l) g) acc)
              )
              from_v
            return ()

predDisjoint :: S.Set Int -> ConGraph -> M.Map (DataType Name) (M.Map Int (M.Map (K L) GuardSet))
predDisjoint is (ConGraph sgs) = M.map (predTree is) sgs

-- Collect preds of a intermediate nodes i
predTree :: S.Set Int -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map Int (M.Map (K L) GuardSet)
predTree is sg = M.fromSet (\i -> M.mapMaybeWithKey (\l rs -> guard (interface l) >> M.lookup (Dom i) rs) sg) is
  where
    interface :: K a -> Bool
    interface Con {} = True
    interface (Dom x) = S.notMember x is

-- Restrict a constraint graph to it's interface and check satisfiability
restrict :: [Int] -> S.Set Int -> ConGraph -> Either (DataType Name, K L, K R) ConGraph
restrict interface inner cg = do
  let (ConGraph cg') = transDisjoint interface cg
  let pre = predDisjoint inner $ ConGraph cg'
  cg'' <-
    M.traverseWithKey
      ( \d ->
          M.traverseMaybeWithKey
            ( \l rs ->
                case l of
                  Dom x | S.member x inner -> return Nothing
                  _ ->
                    Just
                      <$> M.traverseMaybeWithKey
                        ( \r g ->
                            case r of
                              Dom x | S.member x inner -> return Nothing
                              _ -> do
                                let new_guard = applyPreds pre g
                                if safe l r || isEmpty new_guard
                                  then return $ Just new_guard
                                  else Left (d, l, r)
                        )
                        rs
            )
      )
      cg'
  return $ ConGraph cg''
-- -- Fill in blank edges
-- square :: M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
-- square m = M.mapWithKey (\l rgs -> M.union rgs to) m
--   where
--     to = M.fromSet (const bot) (foldMap M.keysSet m)
--
-- -- Make immutable copy of mutable constraint graph
-- freeze :: [Int] -> ConGraph -> Either (K L, K R) ConGraph
-- freeze xs (ConGraph cg) = ConGraph <$> mapM freezeSub cg
--   where
--     freezeSub :: M.Map (K L) (M.Map (K R) GuardSet) -> Either (K L, K R) (M.Map (K L) (M.Map (K R) GuardSet))
--     freezeSub =
--       M.traverseMaybeWithKey
--         ( \l rgs ->
--             if interface l
--               then
--                 Just
--                   <$> M.traverseMaybeWithKey
--                     ( \r g ->
--                         if interface r
--                           then
--                             let new_guard = weaken xs (ConGraph cg) g
--                              in if isEmpty new_guard
--                                   then Right Nothing
--                                   else
--                                     if safe l r
--                                       then Right $ Just $ minimise new_guard
--                                       else Left (l, r)
--                           else return Nothing
--                     )
--                     rgs
--               else return Nothing
--         )
--     interface :: K a -> Bool
--     interface (Dom x) = x `notElem` xs
--     interface _ = True
--
--
-- -- Take the transitive closure of a graph over an internal set
-- trans :: S.Set Int -> ConGraph -> ConGraph
-- trans xs (ConGraph g) = ConGraph $ M.map (\m -> foldr transX m xs) g
--
-- -- Add transitive connections that pass through node x
-- transX :: Int -> M.Map (K L) (M.Map (K R) GuardSet) -> M.Map (K L) (M.Map (K R) GuardSet)
-- transX x m = M.mapWithKey (M.mapWithKey . go) m
--   where
--     go :: K L -> K R -> GuardSet -> GuardSet
--     go l r g = fromMaybe g $ do
--       lgs <- M.lookup l m
--       rgs <- M.lookup (Dom x) m
--       lg <- M.lookup (Dom x) lgs
--       rg <- M.lookup r rgs
--       return (g ||| (lg &&& rg))
--
-- -- Weaken guards containing intermediate variables
-- weaken :: [Int] -> ConGraph -> GuardSet -> GuardSet
-- weaken xs (ConGraph cg) gs = bind gs $ \(Guard g) ->
--   M.foldrWithKey
--     ( \d xks acc ->
--         case M.lookup d cg of
--           Nothing -> acc
--           Just sg ->
--             S.foldr
--               ( \(x, k) acc ->
--                   if x `elem` xs
--                     then
--                       M.foldrWithKey
--                         ( \l g acc' ->
--                             case l of
--                               Dom y
--                                 | y `elem` xs -> acc'
--                                 | otherwise -> (g &&& dom [k] y d) ||| acc'
--                               Con k' _
--                                 | k == k' -> g ||| acc'
--                                 | otherwise -> acc'
--                         )
--                         acc
--                         $ M.mapMaybe (M.lookup (Dom x)) sg
--                     else dom [k] x d &&& acc
--               )
--               acc
--               xks
--     )
--     top
--     g
--
-- -- Apply existing preds and then insert
-- updatePreds :: Int -> M.Map (DataType Name) (M.Map (K L) GuardSet) -> M.Map Int (M.Map (DataType Name) (M.Map (K L) GuardSet)) -> M.Map Int (M.Map (DataType Name) (M.Map (K L) GuardSet))
-- updatePreds x x_preds preds =
--   let x_preds' = M.map (M.map (applyPreds preds)) x_preds
--    in M.insert x x_preds' preds
