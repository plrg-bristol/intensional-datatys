{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Constraints
  ( Side (..),
    K (..),
    safe,
    toAtomic,
    constraintLoc,
    cons,
  )
where

import Binary
import Data.Hashable
import GhcPlugins hiding (L)
import Types
import Unique
import Prelude hiding ((<>))

data Side = L | R

-- An atomic constructor set with a location tag
data K (s :: Side) where
  Dom :: RVar -> K s
  Set :: UniqSet Name -> SrcSpan -> K 'R
  Con :: Name -> SrcSpan -> K 'L

-- Disregard location in comparison
instance Eq (K s) where
  Dom x == Dom x' = x == x'
  Set s _ == Set s' _ = s == s'
  Con k _ == Con k' _ = k == k'
  _ == _ = False

instance Ord (K s) where
  Dom x <= Dom x' = x <= x'
  Set k _ <= Set k' _ = nonDetEltsUniqSet k <= nonDetEltsUniqSet k'
  Con k _ <= Con k' _ = k <= k'
  Dom _ <= _ = True
  _ <= _ = False

instance Hashable Unique where
  hashWithSalt s = hashWithSalt s . getKey

instance Hashable Name where
  hashWithSalt s = hashWithSalt s . getUnique

instance Hashable (K s) where
  hashWithSalt s (Dom x) = hashWithSalt s x
  hashWithSalt s (Set n _) = hashWithSalt s $ nonDetKeysUniqSet n
  hashWithSalt s (Con n _) = hashWithSalt s $ getUnique n

instance Outputable (K s) where
  ppr (Dom x) = text "dom" <> parens (ppr x)
  ppr (Con k _) = ppr k
  ppr (Set ks _)
    | isEmptyUniqSet ks = unicodeSyntax (char '∅') (ppr "{}")
    | otherwise = pprWithBars ppr (nonDetEltsUniqSet ks)

instance Binary (K 'L) where
  put_ bh (Dom x) = put_ bh True >> put_ bh x
  put_ bh (Con k l) = put_ bh False >> put_ bh k >> put_ bh l

  get bh = do
    n <- get bh
    if n
      then do
        x <- get bh
        return (Dom x)
      else do
        k <- get bh
        l <- get bh
        return (Con k l)

instance Binary (K 'R) where
  put_ bh (Dom x) = put_ bh True >> put_ bh x
  put_ bh (Set s l) = put_ bh False >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh = do
    n <- get bh
    if n
      then Dom <$> get bh
      else Set . mkUniqSet <$> get bh <*> get bh

instance Monad m => Refined (K l) m where
  domain (Dom x) = return [x]
  domain _ = return []

  rename x y (Dom x')
    | x == x' = return (Dom y)
  rename _ _ c = return c

-- Is a pair of constructor sets safe?
safe :: K l -> K r -> Bool
safe (Set ks _) (Set ks' _) = uniqSetAll (`elementOfUniqSet` ks') ks
safe (Con k _) (Set ks _) = elementOfUniqSet k ks
safe (Set ks _) (Con k _) = nonDetEltsUniqSet ks == [k]
safe _ _ = True

-- Convert constraint to atomic form
toAtomic :: K l -> K r -> Maybe [(K 'L, K 'R)]
toAtomic (Dom x) (Dom y)
  | x /= y = Just [(Dom x, Dom y)]
toAtomic (Dom x) (Set k l) =
  Just [(Dom x, Set k l)]
toAtomic (Set ks l) (Dom x) =
  Just [(Con k l, Dom x) | k <- nonDetEltsUniqSet ks]
toAtomic (Con k l) (Dom x) =
  Just [(Con k l, Dom x)]
toAtomic k1 k2
  | safe k1 k2 = Just []
  | otherwise = Nothing

constraintLoc :: K l -> Maybe SrcSpan
constraintLoc (Dom _) = Nothing
constraintLoc (Set _ l) = Just l
constraintLoc (Con _ l) = Just l

cons :: K l -> [Name]
cons (Dom _) = []
cons (Con k _) = [k]
cons (Set ks _) = nonDetEltsUniqSet ks