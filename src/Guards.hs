{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}

module Guards
  ( GsM (..),
    Memo,
    Node,
    ID,
    Guard (..),
    GuardSet (Top, Bot),
    singleton,
    dom,
    (|||),
    (&&&),
    toList,
    fromList,
    isEmpty,
    applyPreds,
  )
where

import qualified Binary as B
import Constraints
import Control.Monad.State
import qualified Data.HashMap.Lazy as H
import Data.Hashable
import qualified Data.List as L
import Data.Maybe
import DataTypes
import GHC.Generics
import GhcPlugins hiding (L, isEmpty, singleton)
import Types
import Prelude hiding ((<>))

-- A GuardState monad contins a directed acyclic graph of nodes
class MonadState state m => GsM state s m | m -> state, m -> s where
  lookupNode :: ID -> m (Node s)
  lookupHash :: Node s -> m (Maybe ID)
  freshNode :: Node s -> m ID

  -- Only run an operation if its new
  memo :: Memo s -> m (GuardSet s) -> m (GuardSet s)

-- Operation DSL
data Memo s
  = And {-# UNPACK #-} !ID {-# UNPACK #-} !ID
  | Or {-# UNPACK #-} !ID {-# UNPACK #-} !ID
  | Ite {-# UNPACK #-} !(GuardSet s) {-# UNPACK #-} !(GuardSet s) {-# UNPACK #-} !(GuardSet s)
  deriving (Eq, Ord, Generic)

instance Hashable (Memo s)

-- A guard atom, i.e. a set of constraints of the form k in (X, d)
data Guard = Guard Name RVar (DataType Name)
  deriving (Eq, Ord, Generic)

instance Hashable Guard

instance Outputable Guard where
  ppr (Guard k x d) = ppr k <+> unicodeSyntax (char '∈') (text "in") <+> ppr x <> parens (ppr d)

instance B.Binary Guard where
  put_ bh (Guard k x d) = B.put_ bh k *> B.put_ bh x *> B.put_ bh d
  get bh = Guard <$> B.get bh <*> B.get bh <*> B.get bh

instance Monad m => Refined Guard m where
  domain (Guard _ x _) = return [x]
  rename x y (Guard k z d)
    | x == z = return (Guard k y d)
    | otherwise = return (Guard k z d)

-- An internal node with a unique ID
type ID = Int

data Node s
  = Node
      { atom :: Guard,
        lo, hi :: GuardSet s
      }
  deriving (Eq, Generic)

instance Hashable (Node s)

-- A stateful set of possible guards
data GuardSet s
  = Top
  | Bot
  | ID ID
  deriving (Eq, Ord, Generic)

instance Hashable (GuardSet s)

instance GsM state s m => Refined (GuardSet s) m where
  domain (ID i) = do
    Node g l r <- lookupNode i
    dg <- domain g
    dl <- domain l
    dr <- domain r
    return (dg `L.union` dl `L.union` dr)
  domain _ = return []

  rename x y = bind (rename x y >=> singleton)

  renameAll xys (ID i) = do
    Node g l r <- lookupNode i
    g' <- renameAll xys g
    l' <- renameAll xys l
    r' <- renameAll xys r
    mkGuardSet $ Node g' l' r'
  renameAll _ g = return g

-- Construct a guardset from a guard
singleton :: GsM state s m => Guard -> m (GuardSet s)
singleton g = mkGuardSet $ Node g Bot Top

-- Constrain a refinement variable to contain one of the supplied constructors
dom :: GsM state s m => [Name] -> RVar -> DataType Name -> m (GuardSet s)
dom ks x d = do
  alts <-
    mapM singleton [Guard k x d | k <- ks]
  foldM (|||) Bot alts

-- Make a GuardSet from a node (or reuse an existing node)
mkGuardSet :: GsM state s m => Node s -> m (GuardSet s)
mkGuardSet n
  | lo n == hi n = return (lo n) -- Skip redundant nodes
  | otherwise =
    lookupHash n >>= \case
      Just j -> return (ID j) -- Node sharing
      Nothing -> ID <$> freshNode n

-- Combine two alternative guards
(|||) :: GsM state s m => GuardSet s -> GuardSet s -> m (GuardSet s)
(|||) Top _ = return Top
(|||) _ Top = return Top
(|||) Bot q = return q
(|||) p Bot = return p
(|||) p@(ID i) q@(ID j) =
  memo (Or i j) $ do
    n <- lookupNode i
    m <- lookupNode j
    case compare (atom n) (atom m) of
      LT -> do
        lo' <- lo n ||| q
        hi' <- hi n ||| q
        mkGuardSet $ Node (atom n) lo' hi'
      EQ -> do
        lo' <- lo n ||| lo m
        hi' <- hi n ||| hi m
        mkGuardSet $ Node (atom n) lo' hi'
      GT -> do
        lo' <- p ||| lo m
        hi' <- p ||| hi m
        mkGuardSet $ Node (atom m) lo' hi'

-- Take the conjunction of possible guards
(&&&) :: GsM state s m => GuardSet s -> GuardSet s -> m (GuardSet s)
(&&&) Top q = return q
(&&&) p Top = return p
(&&&) Bot _ = return Bot
(&&&) _ Bot = return Bot
(&&&) p@(ID i) q@(ID j) =
  memo (And i j) $ do
    n <- lookupNode i
    m <- lookupNode j
    case compare (atom n) (atom m) of
      LT -> do
        lo' <- lo n &&& q
        hi' <- hi n &&& q
        mkGuardSet $ Node (atom n) lo' hi'
      EQ -> do
        lo' <- lo n &&& lo m
        hi' <- hi n &&& hi m
        mkGuardSet $ Node (atom n) lo' hi'
      GT -> do
        lo' <- p &&& lo m
        hi' <- p &&& hi m
        mkGuardSet $ Node (atom m) lo' hi'

-- If then else
-- ITE x y z = xy + not x z
ite :: GsM state s m => GuardSet s -> GuardSet s -> GuardSet s -> m (GuardSet s)
ite Top t _ = return t
ite Bot _ e = return e
ite g Top e = g ||| e
ite g t Bot = g &&& t
ite p q r =
  memo (Ite p q r) $ do
    x <- fromJust <$> topAtom [p, q, r]
    lon <- restrict x False p
    hin <- restrict x True p
    lom <- restrict x False q
    him <- restrict x True q
    lol <- restrict x False r
    hil <- restrict x True r
    lo' <- ite lon lom lol
    hi' <- ite hin him hil
    mkGuardSet $ Node x lo' hi'

topAtom :: GsM state s m => [GuardSet s] -> m (Maybe Guard)
topAtom [] = return Nothing
topAtom (Top : gs) = topAtom gs
topAtom (Bot : gs) = topAtom gs
topAtom ((ID i) : gs) = do
  n <- lookupNode i
  let x = atom n
  topAtom gs >>= \case
    Nothing -> return (Just x)
    Just y -> return (Just (max x y))

-- Assign a guard some value
restrict :: GsM state s m => Guard -> Bool -> GuardSet s -> m (GuardSet s)
restrict _ _ Top = return Top
restrict _ _ Bot = return Bot
restrict g b p@(ID i) = do
  n <- lookupNode i
  case compare (atom n) g of
    LT -> return p
    EQ
      | b -> return (hi n)
      | otherwise -> return (lo n)
    GT -> do
      hn <- restrict g b (hi n)
      ln <- restrict g b (lo n)
      mkGuardSet $ Node (atom n) ln hn

bind :: GsM state s m => (Guard -> m (GuardSet s)) -> GuardSet s -> m (GuardSet s)
bind _ Top = return Top
bind _ Bot = return Bot
bind f (ID i) = do
  n <- lookupNode i
  fn <- f (atom n)
  lo' <- bind f (lo n)
  hi' <- bind f (hi n)
  ite fn hi' lo'

-- The predecessors of a particular refinement variable at a datatype
type PredMap s = H.HashMap (DataType Name) (H.HashMap RVar (H.HashMap (K 'L) (GuardSet s)))

applyPreds :: GsM state s m => PredMap s -> GuardSet s -> m (GuardSet s)
applyPreds preds =
  bind
    ( \g@(Guard k x d) ->
        case H.lookup d preds >>= H.lookup x of
          Nothing -> singleton g
          Just g_preds ->
            H.foldrWithKey
              ( \p pg macc -> do
                  acc <- macc
                  case p of
                    Dom y -> do
                      n <- singleton (Guard k y d)
                      n' <- n &&& pg
                      n' ||| acc
                    Con k' _
                      | k == k' -> pg ||| acc
                      | otherwise -> return acc
              )
              (return Bot)
              g_preds
    )

-- Collapse a GuardSet to some summary value
fold :: GsM state s m => (Guard -> a -> a -> a) -> a -> a -> GuardSet s -> m a
fold _ _ bt Top = return bt
fold _ bb _ Bot = return bb
fold f bb bt (ID i) = do
  Node a l h <- lookupNode i
  l' <- fold f bb bt l
  h' <- fold f bb bt h
  return (f a l' h')

-- Collapse a GuardSet to some summary value
foldM' :: GsM state s m => (Guard -> a -> a -> m a) -> a -> a -> GuardSet s -> m a
foldM' _ _ bt Top = return bt
foldM' _ bb _ Bot = return bb
foldM' f bb bt (ID i) = do
  Node a l h <- lookupNode i
  l' <- foldM' f bb bt l
  h' <- foldM' f bb bt h
  f a l' h'

-- Convert to DNF
toList :: GsM state s m => GuardSet s -> m [[Guard]]
toList =
  fold
    (\g los his -> [g : gs | gs <- his] ++ los)
    []
    [[]]

-- Convert from DNF
fromList :: GsM state s m => [[Guard]] -> m (GuardSet s)
fromList =
  foldM
    ( \acc gs ->
        foldM (\p g -> singleton g >>= (&&&) p) Top gs >>= (|||) acc
    )
    Bot

-- Is the guard satisfiable?
isEmpty :: GsM state s m => GuardSet s -> m Bool
isEmpty = fold (const (&&)) True False
