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
import ConGraph
import qualified Data.List as L
import GhcPlugins hiding (Type, empty, pprTyVars)
import Types
import Prelude hiding ((<>))

-- Constrained polymorphic types
type Scheme s = SchemeGen (Type 'T) (ConGraph s)

type IfScheme = SchemeGen (IfType 'T) IfConGraph

data SchemeGen t g
  = Scheme
      { tyvars :: [Name],
        boundvs :: [Int],
        body :: t,
        constraints :: Maybe g
      }

instance Binary IfScheme where
  put_ bh scheme =
    put_ bh (tyvars scheme)
      >> put_ bh (boundvs scheme)
      >> put_ bh (body scheme)
      >> put_ bh (constraints scheme)

  get bh = Scheme <$> get bh <*> get bh <*> get bh <*> get bh

instance Outputable d => Outputable (SchemeGen d IfConGraph) where
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

instance (Monad m, Refined d m, Refined g m) => Refined (SchemeGen d g) m where
  domain s = do
    db <- domain (body s)
    case constraints s of
      Nothing -> return (db L.\\ boundvs s)
      Just cg -> do
        dcg <- domain cg
        return ((db `L.union` dcg) L.\\ boundvs s)

  rename x y s
    | x `elem` boundvs s = return s
    | y `elem` boundvs s = pprPanic "Alpha renaming of polymorphic types is not implemented!!" $ ppr (x, y)
    | otherwise = do
      bod <- rename x y $ body s
      cg <- mapM (rename x y) $ constraints s
      return $
        Scheme
          { tyvars = tyvars s,
            boundvs = boundvs s,
            body = bod,
            constraints = cg
          }

  renameAll xys s = do
    bod <- renameAll xys $ body s
    cg <- mapM (renameAll xys) $ constraints s
    return $
      Scheme
        { tyvars = tyvars s,
          boundvs = boundvs s,
          body = bod,
          constraints = cg
        }

pattern Mono :: t -> SchemeGen t g
pattern Mono t =
  Scheme
    { tyvars = [],
      boundvs = [],
      body = t,
      constraints = Nothing
    }

pattern Forall :: [Name] -> t -> SchemeGen t g
pattern Forall as t =
  Scheme
    { tyvars = as,
      boundvs = [],
      body = t,
      constraints = Nothing
    }

-- Demand a monomorphic type
mono :: Scheme s -> Type 'T
mono (Mono t) = t
mono _ = Ambiguous
