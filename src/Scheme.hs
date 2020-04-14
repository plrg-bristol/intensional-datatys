{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Scheme (
  Scheme(..),
  pattern Mono,
  pattern Forall,
  mono,
) where

import Prelude hiding ((<>))
import qualified Data.List as L

import Types
import ConGraph

import Name
import Binary
import Outputable hiding (empty)

-- Constrained polymorphic types
data Scheme d = Scheme {
    tyvars      :: [Name],
    boundvs     :: [Int],
    body        :: Type T d,
    constraints :: Maybe ConGraph
  }
  deriving Functor

instance Refined (Type T d) => Refined (Scheme d) where
  freevs s =
    case constraints s of
      Nothing -> freevs (body s) L.\\ boundvs s
      Just cs -> (freevs (body s) `L.union` freevs cs) L.\\ boundvs s

  rename x y s
    | x `elem` boundvs s = s
    | y `elem` boundvs s = pprPanic "Unimplemented!" $ ppr (x, y)
    | otherwise = Scheme {
        tyvars      = tyvars s,
        boundvs     = boundvs s,
        body        = rename x y $ body s,
        constraints = rename x y <$> constraints s
      }

instance Outputable d => Outputable (Scheme d) where
  ppr scheme =
    case constraints scheme of
      Just cs
        | cs /= empty -> hang (pprTyVars <> pprConVars <> ppr (body scheme))
                            2 (hang (text "where") 2 (ppr cs))
      _ -> pprTyVars <> pprConVars <> ppr (body scheme)
    where
      pprTyVars
        | null (tyvars scheme) = text ""
        | otherwise            = forAllLit <+> fsep (map ppr $ tyvars scheme) <> dot
      pprConVars
        | null (boundvs scheme) = text ""
        | otherwise             = forAllLit <+> fsep (ppr <$> boundvs scheme) <> dot

instance Binary (Type T d) => Binary (Scheme d) where
  put_ bh scheme = do
    put_ bh $ tyvars scheme
    put_ bh $ boundvs scheme
    put_ bh $ body scheme
    put_ bh $ constraints scheme

  get bh = do
    as <- get bh
    q  <- get bh
    cs <- get bh
    t  <- get bh
    return $ Scheme { tyvars = as, boundvs = q, body = t, constraints = cs }

pattern Mono :: Type T d -> Scheme d
pattern Mono t = Scheme {
  tyvars      = [],
  boundvs     = [],
  body        = t,
  constraints = Nothing
}

pattern Forall :: [Name] -> Type T d -> Scheme d
pattern Forall as t = Scheme {
  tyvars      = as,
  boundvs     = [],
  body        = t,
  constraints = Nothing
}

-- Demand a monomorphic type
mono :: Outputable d => Scheme d -> Type T d
mono (Mono t) = t
mono s        = pprPanic "Higher rank types are unimplemented!" $ ppr s
