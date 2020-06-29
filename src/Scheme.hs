{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}

module Scheme
  ( Scheme,
    SchemeGen (..),
    pattern Forall,
    mono,
  )
where

import Binary
import Constraints
import GhcPlugins
import Types

type Scheme = SchemeGen TyCon

-- Constrained polymorphic types
data SchemeGen d
  = Scheme
      { tyvars :: [Name],
        boundvs :: [Int],
        body :: TypeGen d,
        constraints :: ConstraintSet
      }
  deriving (Functor, Foldable, Traversable)

{-# COMPLETE Forall #-}

pattern Forall :: [Name] -> TypeGen d -> SchemeGen d
pattern Forall as t <-
  Scheme as _ t _
  where
    Forall as t = Scheme as [] t mempty

instance Outputable d => Outputable (SchemeGen d) where
  ppr scheme
    | constraints scheme /= mempty =
      hang
        (hcat [pprTyQuant, dot, pprConQuant, dot, ppr (body scheme)])
        2
        (hang (text "where") 2 (ppr (constraints scheme)))
    | otherwise = hcat [pprTyQuant, pprConQuant, ppr (body scheme)]
    where
      pprTyQuant
        | null (tyvars scheme) = empty
        | otherwise = hcat [forAllLit <+> fsep (map ppr $ tyvars scheme), dot]
      pprConQuant
        | null (boundvs scheme) = empty
        | otherwise = hcat [forAllLit <+> fsep (ppr <$> boundvs scheme), dot]

instance Binary d => Binary (SchemeGen d) where
  put_ bh scheme =
    put_ bh (tyvars scheme)
      >> put_ bh (boundvs scheme)
      >> put_ bh (body scheme)
      >> put_ bh (constraints scheme)

  get bh = Scheme <$> get bh <*> get bh <*> get bh <*> get bh

instance Refined (SchemeGen d) where
  domain s = domain (body s)

  rename x y s
    | x `elem` boundvs s = s
    | y `elem` boundvs s = pprPanic "Alpha renaming of polymorphic types is not implemented!" $ ppr (x, y)
    | otherwise =
      Scheme
        { tyvars = tyvars s,
          boundvs = boundvs s,
          body = rename x y $ body s,
          constraints = rename x y (constraints s)
        }

-- Demand a monomorphic type
mono :: SchemeGen d -> TypeGen d
mono (Forall [] t) = t
mono _ = Ambiguous
