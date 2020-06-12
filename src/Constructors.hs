{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

module Constructors
  ( Side (..),
    K (..),
    safe,
    toAtomic,
    srcSpan,
    cons,
  )
where

import Binary
import Data.Hashable
import qualified Data.IntSet as I
import DataTypes
import GhcPlugins hiding (L)
import Types
import Unique
import Prelude hiding ((<>))

data Side = L | R

-- An atomic constructor set with a location tag
data K (s :: Side) where
  Dom :: RVar -> DataType Name -> K s
  Set :: UniqSet Name -> SrcSpan -> K 'R
  Con :: Name -> SrcSpan -> K 'L

-- Disregard location in comparison
instance Eq (K s) where
  Dom x d == Dom x' d' = x == x' && d == d'
  Set s _ == Set s' _ = s == s'
  Con k _ == Con k' _ = k == k'
  _ == _ = False

-- instance Ord (K s) where
--   Dom x d <= Dom x' d' = x <= x'
--   Set k _ <= Set k' _ = nonDetEltsUniqSet k <= nonDetEltsUniqSet k'
--   Con k _ <= Con k' _ = k <= k'
--   Dom _ <= _ = True
--   _ <= _ = False

-- instance Hashable Unique where
--   hashWithSalt s = hashWithSalt s . getKey

-- instance Hashable Name where
--   hashWithSalt s = hashWithSalt s . getUnique

instance Hashable (K s) where
  hashWithSalt s (Dom x d) = hashWithSalt s (x, getKey . getUnique <$> d)
  hashWithSalt s (Set ks _) = hashWithSalt s $ getKey <$> nonDetKeysUniqSet ks
  hashWithSalt s (Con k _) = hashWithSalt s $ getKey $ getUnique k

instance Outputable (K s) where
  ppr (Dom x d) = text "dom" <> parens (ppr x <> parens (ppr d))
  ppr (Con k _) = ppr k
  ppr (Set ks _)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (text "{}")
    | otherwise = pprWithBars ppr (nonDetEltsUniqSet ks)

instance Binary (K 'L) where
  put_ bh (Dom x d) = put_ bh True >> put_ bh x >> put_ bh d
  put_ bh (Con k l) = put_ bh False >> put_ bh k >> put_ bh l

  get bh =
    get bh >>= \case
      True -> Dom <$> get bh <*> get bh
      False -> Con <$> get bh <*> get bh

instance Binary (K 'R) where
  put_ bh (Dom x d) = put_ bh True >> put_ bh x >> put_ bh d
  put_ bh (Set s l) = put_ bh False >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh =
    get bh >>= \case
      True -> Dom <$> get bh <*> get bh
      False -> Set . mkUniqSet <$> get bh <*> get bh

instance Refined (K l) where
  domain (Dom x _) = I.singleton x
  domain _ = I.empty

  rename x y (Dom x' d)
    | x == x' = Dom y d
  rename _ _ c = c

-- Is a pair of constructor sets safe?
safe :: K l -> K r -> Bool
safe (Set ks _) (Set ks' _) = uniqSetAll (`elementOfUniqSet` ks') ks
safe (Con k _) (Set ks _) = elementOfUniqSet k ks
safe (Set ks _) (Con k _) = nonDetEltsUniqSet ks == [k]
safe _ _ = True

-- Convert constraint to atomic form
toAtomic :: K l -> K r -> Maybe [(K 'L, K 'R)]
toAtomic (Dom x d) (Dom y d')
  | x /= y = Just [(Dom x d, Dom y d')]
toAtomic (Dom x d) (Set k l) =
  Just [(Dom x d, Set k l)]
toAtomic (Set ks l) (Dom x d) =
  Just [(Con k l, Dom x d) | k <- nonDetEltsUniqSet ks]
toAtomic (Con k l) (Dom x d) =
  Just [(Con k l, Dom x d)]
toAtomic k1 k2
  | safe k1 k2 = Just []
  | otherwise = Nothing

srcSpan :: K l -> Maybe SrcSpan
srcSpan (Dom _ _) = Nothing
srcSpan (Set _ l) = Just l
srcSpan (Con _ l) = Just l

cons :: K l -> [Name]
cons (Dom _ _) = []
cons (Con k _) = [k]
cons (Set ks _) = nonDetEltsUniqSet ks