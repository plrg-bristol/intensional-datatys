{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

module Self.Constructors
  ( Side (..),
    K (..),
    toAtomic,
  )
where

import Binary
import Data.Hashable
import GhcPlugins hiding (L)
import Self.Types
import Unique

instance Hashable Unique where
  hashWithSalt s = hashWithSalt s . getKey

instance Hashable Name where
  hashWithSalt s = hashWithSalt s . getUnique

data Side = L | R

-- A constructor set with a location tag
data K (s :: Side) where
  Dom :: DataType Name -> K s
  Con :: Name -> SrcSpan -> K 'L
  Set :: UniqSet Name -> SrcSpan -> K 'R

-- Disregard location in comparison
instance Eq (K s) where
  Dom d == Dom d' = d == d'
  Con k _ == Con k' _ = k == k'
  Set s _ == Set s' _ = s == s'
  _ == _ = False

instance Hashable (K s) where
  hashWithSalt s (Dom d) = hashWithSalt s d
  hashWithSalt s (Con k _) = hashWithSalt s k
  hashWithSalt s (Set ks _) = hashWithSalt s (nonDetKeysUniqSet ks)

instance Outputable (K s) where
  ppr (Dom d) = ppr d
  ppr (Con k _) = ppr k
  ppr (Set ks _) = hcat [char '{', pprWithBars ppr (nonDetEltsUniqSet ks), char '}']

instance Binary (K 'L) where
  put_ bh (Dom d) = put_ bh False >> put_ bh d
  put_ bh (Con k l) = put_ bh True >> put_ bh k >> put_ bh l

  get bh =
    get bh >>= \case
      False -> Dom <$> get bh
      True -> Con <$> get bh <*> get bh

instance Binary (K 'R) where
  put_ bh (Dom d) = put_ bh False >> put_ bh d
  put_ bh (Set s l) = put_ bh True >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh =
    get bh >>= \case
      False -> Dom <$> get bh
      True -> Set . mkUniqSet <$> get bh <*> get bh

instance Refined (K l) where
  domain (Dom d) = domain d
  domain _ = mempty

  rename x y (Dom d) = Dom (rename x y d)
  rename _ _ s = s

-- Convert constraint to atomic form
toAtomic :: K l -> K r -> [(K 'L, K 'R)]
toAtomic (Dom d) (Dom d')
  | d == d' = []
  | otherwise = [(Dom d, Dom d')]
toAtomic (Dom d) (Con k l) =
  [(Dom d, Set (unitUniqSet k) l)]
toAtomic (Dom d) (Set ks l) =
  [(Dom d, Set ks l)]
toAtomic (Con k l) (Dom d) =
  [(Con k l, Dom d)]
toAtomic (Con k l) (Con k' l')
  | k == k' = []
  | otherwise = [(Con k l, Set emptyUniqSet l')]
toAtomic (Con k l) (Set ks l')
  | elementOfUniqSet k ks = []
  | otherwise = [(Con k l, Set emptyUniqSet l')]
toAtomic (Set ks l) (Dom d) =
  [(Con k l, Dom d) | k <- nonDetEltsUniqSet ks]
toAtomic (Set ks l) (Con k l') =
  [(Con k l, Set emptyUniqSet l') | k' <- nonDetEltsUniqSet ks, k' /= k]
toAtomic (Set ks l) (Set ks' l') =
  [(Con k l, Set emptyUniqSet l') | k <- nonDetEltsUniqSet ks, not (elementOfUniqSet k ks')]
