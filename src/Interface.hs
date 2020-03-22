{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Interface (
) where

import qualified Data.Set as S

import Binary
import UniqSet

import Types
import Scheme
import Guard
import ConGraph
import IfaceType

instance (Binary (Type e d), Binary c) => Binary (Scheme e d c) where
  put_ bh (Scheme { tyvars = as, body = t, constraints = cs }) = do
    put_ bh as
    put_ bh cs
    put_ bh t

  get bh = do
    as <- get bh
    cs <- get bh
    t  <- get bh
    return $ Scheme { tyvars = as, body = t, constraints = cs }

instance Binary ConGraph where
  put_ bh cs = put_ bh (toList cs)
  get bh = fromList <$> get bh

instance Binary K where
  put_ bh (Dom x d) = put_ bh (0 :: Int) >> put_ bh x >> put_ bh d
  put_ bh (Set s l) = put_ bh (1 :: Int) >> put_ bh (nonDetEltsUniqSet s) >> put_ bh l

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> do
        x <- get bh
        d <- get bh
        return (Dom x d)
      1 -> do
        s <- get bh
        l <- get bh
        return (Set (mkUniqSet s) l)

instance Binary Guard where
  put_ bh (Guard m) = put_ bh (S.toList m)
  get bh = Guard . S.fromList <$> get bh

instance Binary (Type T IfaceTyCon) where
  put_ bh (Var a)      = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b)    = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Base b as)  = put_ bh (2 :: Int) >> put_ bh b >> put_ bh as
  put_ bh (Inj x d as) = put_ bh (4 :: Int) >> put_ bh x >> put_ bh d >> put_ bh as
  put_ bh (a :=> b)    = put_ bh (5 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l)      = put_ bh (6 :: Int) >> put_ bh l

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> Var <$> get bh
      1 -> App <$> get bh <*> get bh
      2 -> Base <$> get bh <*> get bh
      4 -> Inj <$> get bh <*> get bh <*> get bh
      5 -> (:=>) <$> get bh <*> get bh
      6 -> Lit <$> get bh

instance Binary (Type S IfaceTyCon) where
  put_ bh (Var a)      = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b)    = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Base b as)  = put_ bh (2 :: Int) >> put_ bh b >> put_ bh as
  put_ bh (Data d as)  = put_ bh (3 :: Int) >> put_ bh d >> put_ bh as
  put_ bh (a :=> b)    = put_ bh (5 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l)      = put_ bh (6 :: Int) >> put_ bh l

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> Var <$> get bh
      1 -> App <$> get bh <*> get bh
      2 -> Base <$> get bh <*> get bh
      3 -> Data <$> get bh <*> get bh
      5 -> (:=>) <$> get bh <*> get bh
      6 -> Lit <$> get bh
