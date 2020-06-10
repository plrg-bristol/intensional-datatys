{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}

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
import Constructors
import GhcPlugins hiding (Type, empty, pprTyVars)
import Types
import Prelude hiding ((<>))

-- Constrained polymorphic types
type Scheme = SchemeGen (Type 'T)

type IfScheme = SchemeGen (IfType 'T)

data SchemeGen t
  = Scheme
      { tyvars :: [Name],
        boundvs :: [Int],
        body :: t,
        constraints :: Maybe ConstraintSet
      }
  deriving (Functor)

instance Binary IfScheme where
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

instance Refined d => Refined (SchemeGen d) where
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

-- renameAll xys s = do
--   bod <- renameAll xys $ body s
--   cg <- mapM (renameAll xys) $ constraints s
--   return $
--     Scheme
--       { tyvars = tyvars s,
--         boundvs = boundvs s,
--         body = bod,
--         constraints = cg
--       }

pattern Mono :: t -> SchemeGen t
pattern Mono t =
  Scheme
    { tyvars = [],
      boundvs = [],
      body = t,
      constraints = Nothing
    }

pattern Forall :: [Name] -> t -> SchemeGen t
pattern Forall as t =
  Scheme
    { tyvars = as,
      boundvs = [],
      body = t,
      constraints = Nothing
    }

-- Demand a monomorphic type
mono :: Scheme -> Type 'T
mono (Mono t) = t
mono _ = Ambiguous
