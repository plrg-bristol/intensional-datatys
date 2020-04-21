{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

module Scheme
  ( Scheme (..),
    pattern Mono,
    pattern Forall,
    mono,
  )
where

import Binary
import ConGraph
import Control.Monad
import qualified Data.IntSet as I
import qualified Data.List as L
import Name
import Outputable hiding (empty)
import Types
import Prelude hiding ((<>))

-- Constrained polymorphic types
data Scheme d = Scheme
  { tyvars :: [Name],
    boundvs :: [Int],
    body :: Type T d,
    constraints :: Maybe ConGraph
  }
  deriving (Functor)

instance Refined (Type T d) => Refined (Scheme d) where
  freevs s = freevs (body s) L.\\ boundvs s

  rename x y s
    | x `elem` boundvs s = s
    | y `elem` boundvs s = pprPanic "Unimplemented!" $ ppr (x, y)
    | otherwise =
      Scheme
        { tyvars = tyvars s,
          boundvs = boundvs s,
          body = rename x y $ body s,
          constraints = rename x y <$> constraints s
        }

instance Outputable d => Outputable (Scheme d) where
  ppr scheme =
    case constraints scheme of
      Just cs
        | cs /= empty ->
          hang
            (pprTyVars <> pprConVars <> ppr (body scheme))
            2
            (hang (text "where") 2 (ppr cs))
      _ -> pprTyVars <> pprConVars <> ppr (body scheme)
    where
      pprTyVars
        | null (tyvars scheme) = text ""
        | otherwise = forAllLit <+> fsep (map ppr $ tyvars scheme) <> dot
      pprConVars
        | null (boundvs scheme) = text ""
        | otherwise = forAllLit <+> fsep (ppr <$> boundvs scheme) <> dot

instance Binary (Type T d) => Binary (Scheme d) where
  put_ bh scheme = put_ bh (tyvars scheme) >> put_ bh (boundvs scheme) >> put_ bh (body scheme) >> put_ bh (constraints scheme)

  get bh = Scheme <$> get bh <*> get bh <*> get bh <*> get bh

pattern Mono :: Type T d -> Scheme d
pattern Mono t =
  Scheme
    { tyvars = [],
      boundvs = [],
      body = t,
      constraints = Nothing
    }

pattern Forall :: [Name] -> Type T d -> Scheme d
pattern Forall as t =
  Scheme
    { tyvars = as,
      boundvs = [],
      body = t,
      constraints = Nothing
    }

-- Demand a monomorphic type
mono :: Outputable d => Scheme d -> Type T d
mono (Mono t) = t
mono s = pprPanic "Higher rank types are unimplemented!" $ ppr s
