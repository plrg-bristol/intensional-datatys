{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

module Intensional.Constructors
  ( Side (..),
    K (..),
    ConL,
    ConR,
    toAtomic,
    getLocation
  )
where

import Binary
import Data.Hashable
import GhcPlugins hiding (L)
import Intensional.Types
import Unique

instance Hashable Unique where
  hashWithSalt s = hashWithSalt s . getKey

instance Hashable Name where
  hashWithSalt s = hashWithSalt s . getUnique

data Side = L | R

-- A constructor set with a location tag
-- We include the srcSpan as part of the
-- identity so that multiple errors with 
-- the same constructor in different program
-- locations are treated seperately.
data K (s :: Side) where
  Dom :: DataType Name -> K s
  Con :: Name -> SrcSpan -> K 'L
  Set :: UniqSet Name -> SrcSpan -> K 'R

type ConL = K 'L
type ConR = K 'R

-- Don't disregard location in comparison
-- i.e. distinguish between different sources
-- and sinks
instance Eq (K s) where
  Dom d == Dom d' = d == d'
  Con k l == Con k' l' = k == k' && l == l'
  Set s l == Set s' l' = s == s' && l == l'
  _ == _ = False

instance Hashable (K s) where
  hashWithSalt s (Dom d) = hashWithSalt s d
  hashWithSalt s (Con k _) = hashWithSalt s k
  hashWithSalt s (Set ks _) = hashWithSalt s (nonDetKeysUniqSet ks)

instance Outputable (K s) where
  ppr = prpr ppr

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
      True -> do
        s <- mkUniqSet <$> get bh
        l <- get bh
        return (Set s l)

instance Refined (K l) where
  domain (Dom d) = domain d
  domain _ = mempty

  rename x y (Dom d) = Dom (rename x y d)
  rename _ _ s = s

  prpr m (Dom (Inj x d)) = m x GhcPlugins.<> parens (ppr d)
  prpr _ (Dom (Base _))  = error "Base in constraint."
  prpr _ (Con k _) = ppr k
  prpr _ (Set ks _) = hcat [char '{', pprWithBars ppr (nonDetEltsUniqSet ks), char '}']

{-|
    Assuming @k@ is either a @Con@ or @Set@ atom, 
    @getLocation k@ is the associated span.
-}
getLocation :: K a -> SrcSpan 
getLocation (Con _ s) = s
getLocation (Set _ s) = s
getLocation _         = error "Dom constructors have no location."

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
