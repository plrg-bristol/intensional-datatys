{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Scheme
  ( Scheme (..),
    pattern Mono,
    pattern Forall,
    mono,
    promoteSch,
  )
where

import Binary
import ConGraph
import Data.Bifunctor
import Data.Functor.Identity
import qualified Data.List as L
import DataTypes
import GhcPlugins hiding (Type, empty)
import Guards
import IfaceType
import qualified TyCoRep as Tcr
import Types
import Prelude hiding ((<>))

-- Constrained polymorphic types
data Scheme d g = Scheme
  { tyvars :: [Name],
    boundvs :: [Int],
    body :: Type T d,
    constraints :: Maybe (ConGraphGen g)
  }

deriving instance (Foldable (Scheme d))

deriving instance (Functor (Scheme d))

deriving instance (Traversable (Scheme d))

instance Bifunctor Scheme where
  bimap f g (Scheme ty bvs bod cons) = Scheme ty bvs (fmap f bod) (fmap (fmap g) cons)

instance Outputable d => Outputable (Scheme d [[Guard]]) where
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

instance Binary (Type T d) => Binary (Scheme d [[Guard]]) where
  put_ bh scheme = put_ bh (tyvars scheme) >> put_ bh (boundvs scheme) >> put_ bh (body scheme) >> put_ bh (constraints scheme)

  get bh = Scheme <$> get bh <*> get bh <*> get bh <*> get bh

instance (GsM state s m, Refined g m, Refined (Type T d) Identity) => Refined (Scheme d g) m where
  domain s = do
    let db = runIdentity (domain (body s))
    case constraints s of
      Nothing -> return (db L.\\ boundvs s)
      Just cg -> do
        dcg <- domain cg
        return ((db `L.union` dcg) L.\\ boundvs s)

  rename x y s
    | x `elem` boundvs s = return s
    | y `elem` boundvs s = pprPanic "Alpha renaming of polymorphic types is not implemented!!" $ ppr (x, y)
    | otherwise = do
      let bod = runIdentity (rename x y $ body s)
      cg <- mapM (rename x y) $ constraints s
      return $
        Scheme
          { tyvars = tyvars s,
            boundvs = boundvs s,
            body = bod,
            constraints = cg
          }

pattern Mono :: Type T d -> Scheme d g
pattern Mono t =
  Scheme
    { tyvars = [],
      boundvs = [],
      body = t,
      constraints = Nothing
    }

pattern Forall :: [Name] -> Type T d -> Scheme d g
pattern Forall as t =
  Scheme
    { tyvars = as,
      boundvs = [],
      body = t,
      constraints = Nothing
    }

-- Demand a monomorphic type
mono :: (GsM state s m, Outputable d) => Scheme d (GuardSet s) -> m (Type T d)
mono (Mono t) = return t
mono s = pprPanic "Higher rank types are unimplemented!" . ppr <$> mapM toList s

-- Lift a scheme from interface with the help of a core type
promoteSch :: Tcr.Type -> Scheme IfaceTyCon g -> Scheme TyCon g
promoteSch shape (Scheme bvs tyvs body cs) = Scheme bvs tyvs (promoteTy shape body) cs
