{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module Scheme
  ( Scheme,
    IfScheme,
    SchemeGen (..),
    pattern Mono,
    pattern Forall,
    mono,
  )
where

import Binary
import Constraints
import DataTypes
import GhcPlugins
import IfaceType
import Types

type Scheme = SchemeGen TyCon

type IfScheme = SchemeGen IfaceTyCon

-- Constrained polymorphic types
data SchemeGen d
  = Scheme
      { tyvars :: [Name],
        boundvs :: [Int],
        body :: TypeGen d,
        constraints :: Maybe ConstraintSet
      }
      deriving (Functor)

instance Binary d => Binary (SchemeGen d) where
  put_ bh scheme =
    put_ bh (tyvars scheme)
      >> put_ bh (boundvs scheme)
      >> put_ bh (body scheme)
      >> put_ bh (constraints scheme)

  get bh = Scheme <$> get bh <*> get bh <*> get bh <*> get bh

instance Outputable d => Outputable (SchemeGen d) where
  ppr scheme =
    case constraints scheme of
      Just cs
        | cs /= mempty ->
          hang (hcat [pprTyQuant, dot, pprConQuant, dot, ppr (body scheme)]) 2 (hang (text "where") 2 (ppr cs))
      _ -> hcat [pprTyQuant, dot, pprConQuant, dot, ppr (body scheme)]
    where
      pprTyQuant
        | null (tyvars scheme) = empty
        | otherwise = forAllLit <+> fsep (map ppr $ tyvars scheme)
      pprConQuant
        | null (boundvs scheme) = empty
        | otherwise = forAllLit <+> fsep (ppr <$> boundvs scheme)

instance Refined (SchemeGen d) where
  domain s = domain (body s)

  rename x y s
    | x `elem` boundvs s = s
    | y `elem` boundvs s = pprPanic "Alpha renaming of polymorphic types is not implemented!!" $ ppr (x, y)
    | otherwise =
      Scheme
        { tyvars = tyvars s,
          boundvs = boundvs s,
          body = rename x y $ body s,
          constraints = rename x y <$> constraints s
        }

pattern Mono :: TypeGen d -> SchemeGen d
pattern Mono t =
  Scheme
    { tyvars = [],
      boundvs = [],
      body = t,
      constraints = Nothing
    }

pattern Forall :: [Name] -> TypeGen d -> SchemeGen d
pattern Forall as t =
  Scheme
    { tyvars = as,
      boundvs = [],
      body = t,
      constraints = Nothing
    }

-- Demand a monomorphic type
mono :: SchemeGen d -> TypeGen d
mono (Mono t) = t
mono _ = Ambiguous
