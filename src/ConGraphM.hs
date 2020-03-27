{-# LANGUAGE ScopedTypeVariables #-}

module ConGraphM (
  ConGraphM,
  empty,
  guardWith,
  union,
  insert,
  restrict,
) where

import Prelude hiding (lookup, map)

import Data.Ix
import Data.Maybe
import Data.STRef
import Data.Array.ST hiding (freeze, thaw)
import Data.Array.MArray hiding (freeze, thaw)
import Data.Hashable

import Control.Monad
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Set as S

import Types
import ConGraph

import Name
import Unique
import SrcLoc
import UniqSet
import Outputable hiding (empty)
import Guard

import Control.Monad.ST

data KL =
    Con Name SrcSpan
  | DomL Int
  deriving Eq

data KR =
    SetR (UniqSet Name) SrcSpan
  | DomR Int
  deriving Eq

instance Ord KL
instance Ord KR

instance Hashable Unique where
  hashWithSalt s u = hashWithSalt s (getKey u)

instance Hashable KR where
  hashWithSalt s (DomR x)    = hashWithSalt s x
  hashWithSalt s (SetR ks _) = hashWithSalt s (nonDetKeysUniqSet ks)

instance Hashable KL where
  hashWithSalt s (DomL x)  = hashWithSalt s x
  hashWithSalt s (Con k _) = hashWithSalt s (getUnique k)

safe' :: KL -> KR -> Bool
safe' = undefined

-- Default capacity
cap :: Int
cap = 16

newtype ConGraphM s = ConGraphM (M.Map Name (SubGraph s))

-- A disjoint graph for one datatype
data SubGraph s = SubGraph {
  edges :: STArray s (Int, Int) (M.Map KL (M.Map KR GuardSet)),
  left  :: STRef s (S.Set Int), -- Nodes
  right :: STRef s (S.Set Int)
}

empty :: ST s (SubGraph s)
empty = do
  edges <- newArray ((0, 0), (cap, cap)) M.empty
  left  <- newSTRef S.empty
  right <- newSTRef S.empty
  return (SubGraph edges left right)

-- Insert an edge into a bin
insertBin :: KL -> KR -> GuardSet -> M.Map KL (M.Map KR GuardSet) -> M.Map KL (M.Map KR GuardSet)
insertBin n m e = M.alter go n
  where
    go (Just b) = Just $ M.insertWith (|||) m e b
    go Nothing  = Just $ M.singleton m e

-- Insert a new edge
insertAtomic :: KL -> KR -> GuardSet -> SubGraph s -> ST s ()
insertAtomic n m e g = do
  let i = hash n `mod` cap
  let j = hash m `mod` cap
  ebin <- readArray (edges g) (i, j)
  writeArray (edges g) (i, j) (insertBin n m e ebin)
  modifySTRef (left g) (S.insert i)
  modifySTRef (right g) (S.insert j)

toAtomic :: K -> K -> Maybe (Maybe (Name, [(KL, KR)]))
toAtomic (Dom x d) (Dom y d')
  | d /= d'   = pprPanic "Constraint between types of different shape!" $ ppr (d, d')
  | x == y    = Just Nothing
  | otherwise = Just $ Just (d, [(DomL x, DomR y)])
toAtomic (Dom x d) (Set k l)
              = Just $ Just (d, [(DomL x, SetR k l)])
toAtomic (Set ks l) (Dom x d)
              = Just $ Just (d, [(Con k l, DomR x) | k <- nonDetEltsUniqSet ks])
toAtomic k1 k2
  | safe k1 k2 = Just Nothing
  | otherwise  = Nothing

-- Insert constraint into ConGraphM if satisfiable
insert :: K -> K -> GuardSet -> ConGraphM s -> ST s (Maybe (ConGraphM s))
insert k1 k2 e (ConGraphM cg) =
  case toAtomic k1 k2 of
    Nothing             -> return Nothing
    Just Nothing        -> return $ Just $ ConGraphM cg
    Just (Just (d, cs)) -> Just . ConGraphM <$> M.alterF (go cs) d cg
  where
    go :: [(KL, KR)] -> Maybe (SubGraph s) -> ST s (Maybe (SubGraph s))
    go cs Nothing = do
      new <- empty
      forM_ cs (\(kl, kr) -> insertAtomic kl kr e new)
      return $ Just new
    go cs (Just g) = do
      forM_ cs (\(kl, kr) -> insertAtomic kl kr e g)
      return $ Just g

-- Add the content of the second graph to the first
union :: ConGraphM s -> ConGraphM s -> ST s (ConGraphM s)
union (ConGraphM m) cg = M.foldrWithKey (\d sg curr -> do
  ConGraphM cg' <- curr
  case M.lookup d cg' of
    Just sg' -> do
      l <- readSTRef (left sg)
      l' <- readSTRef (left sg')
      forM_ (S.union l l') $ \i -> do
        r <- readSTRef (right sg)
        r' <- readSTRef (right sg')
        forM_ (S.union r r') $ \j -> do
          gbin <- readArray (edges sg) (i, j)
          hbin <- readArray (edges sg') (i, j)
          writeArray (edges sg') (i, j) (M.unionWith (M.unionWith (|||)) gbin hbin)
      return (ConGraphM cg')
    Nothing -> return $ ConGraphM $ M.insert d sg cg'
  ) (return cg) m

guardWith :: S.Set Name -> Int -> Name -> ConGraphM s -> ST s ()
guardWith ks x d (ConGraphM m) = mapM_ (mapArray (M.map (M.map (dom ks x d &&&))) . edges) m

freeze = undefined

restrict :: S.Set Int -> ConGraphM s -> ST s (Either (KL, KR) ConGraph)
restrict xs cg = runExceptT $ do
  trans xs cg
  weaken xs cg
  freeze cg

trans :: S.Set Int -> ConGraphM s -> ExceptT (KL, KR) (ST s) ()
trans xs (ConGraphM m) = mapM_ (forM_ xs . transX) m

transX :: SubGraph s -> Int -> ExceptT (KL, KR) (ST s) ()
transX sg x = do
  is <- lift $ readSTRef (left sg)
  js <- lift $ readSTRef (right sg)
  forM_ is (\i ->
    forM_ js (\j -> do
      ik_bin <- lift $ readArray (edges sg) (i, hash (DomR x) `mod` cap)
      kj_bin <- lift $ readArray (edges sg) (hash (DomL x) `mod` cap, j)
      -- This should instead consider everying in the ik_bin to kj_bin!!
      case M.lookup (DomL x) kj_bin of
        Nothing        -> return ()
        Just kj_guards ->
          M.foldrWithKey (\n to q -> do
            case M.lookup n ik_bin of
              Nothing        -> q
              Just nk_guards ->
                case M.lookup (DomR x) nk_guards of
                  Nothing -> q
                  Just nkg ->
                    M.foldrWithKey (\m g q' -> do
                      case M.lookup m kj_guards of
                        Nothing -> q'
                        Just kmg -> do
                          let new_guard = nkg &&& kmg
                          if new_guard == bot
                            then q'
                            else
                              if safe' n m
                                then do
                                  lift $ insertAtomic n m (nkg &&& kmg) sg
                                  q'
                                else
                                  throwError (n, m)
                      ) q to
            ) (return ()) ik_bin
      )
    )

preds :: KR -> SubGraph s -> ST s (M.Map KL GuardSet)
preds m g = do
  let j = hash m `mod` cap
  foldM (\k i -> do
    ebin <- readArray (edges g) (i, j)
    return $ M.union (M.map (fromMaybe bot . M.lookup m) ebin) k
    ) M.empty $ range (0, cap)

-- Replace k1 with k2 in a guard and reduce
replace' :: Int -> Name -> KL -> GuardSet -> GuardSet
replace' x d cs (GuardSet gs) = GuardSet $ S.map go gs
  where
    go :: Guard -> Guard
    go (Guard g) =
      case cs of
        DomL y  -> Guard $ M.adjust (S.map (\(x', k) -> if x == x' then (y, k) else (x', k))) d g
        Con k _ -> Guard $ M.adjust (S.filter (/= (x, k))) d g

weaken :: forall s. S.Set Int -> ConGraphM s -> ExceptT (KL, KR) (ST s) ()
weaken xs (ConGraphM cg) = mapM_ weakenX xs
  where
    weakenX :: Int -> ExceptT (KL, KR) (ST s) ()
    weakenX x = do
      let j = hash (DomR x) `mod` cap
      preds <- M.foldrWithKey (\d sg macc -> do
        is <- lift $ readSTRef (left sg)
        acc <- macc
        foldM (\acc' i -> do
          ebin <- lift $ readArray (edges sg) (i, j)
          let go (DomL y) g | y `elem` xs = return Nothing
                            | otherwise   = do
                              pp <- lift $ preds (DomR y) sg
                              if M.null pp
                                then return $ Just (d, g)
                                else return $ Nothing
              go (Con c l) g = return $ Just (d, g)
          preds_x <- M.traverseMaybeWithKey go $ M.map (fromMaybe bot . M.lookup (DomR x)) ebin
          return (M.union (preds_x :: M.Map KL (Name, GuardSet)) acc')
          ) acc is
        ) (return M.empty) cg

      -- Remove x
      mapM_ (\sg -> do
          --modifySTRef (left sg) (S.delete (hash (DomL x) `mod` cap)
          --modifySTRef (right sg) (S.delete (hash (DomR x) `mod` cap))
          lift $ mapArray (M.map (M.delete (DomR x)) . M.delete (DomL x)) (edges sg)
        ) cg

      M.foldrWithKey (\n (d, g) q -> do
        forM_ cg $ \sg ->
          lift $ mapArray (M.map (M.map (\g' -> g' ||| replace' x d n g' &&& g))) (edges sg)
          -- check safetly
        q
        ) (return ()) preds
