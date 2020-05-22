{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveGeneric #-}

module DataTypes
  ( Level (..),
    DataType (..),
    contravariant,
    trivial,
  )
where

import Binary
import Data.Hashable
import GHC.Generics
import GhcPlugins hiding (Expr (..), Type)
import TyCoRep
import Prelude hiding ((<>))

data Level
  = Neutral -- Not unrolled
  | Initial -- Unrolled; Singletons or Non-empty etc.
  | Full -- Unrolled; Infinite or Empty
  deriving (Eq, Ord, Generic)

instance Hashable Level

-- Internal representation of datatypes
data DataType d
  = DataType
      { level :: Level,
        orig :: d
      }
  deriving (Eq, Ord, Functor, Foldable, Traversable, Generic)

instance Hashable d => Hashable (DataType d)

instance Outputable d => Outputable (DataType d) where
  ppr d
    | level d == Initial = char '\'' <> ppr (orig d)
    | otherwise = ppr (orig d)

instance Binary d => Binary (DataType d) where
  put_ bh (DataType Initial d) = put_ bh (0 :: Int) >> put_ bh d
  put_ bh (DataType Full d) = put_ bh (1 :: Int) >> put_ bh d
  put_ bh (DataType Neutral d) = put_ bh (2 :: Int) >> put_ bh d

  get bh = do
    l <- get bh
    case l :: Int of
      0 -> DataType Initial <$> get bh
      1 -> DataType Full <$> get bh
      2 -> DataType Neutral <$> get bh
      _ -> pprPanic "Binary is not a datatype!" (ppr l)

-- Check if a core datatype is contravariant in every type argument
contravariant :: TyCon -> Bool
contravariant = not . all pos . concatMap dataConOrigArgTys . tyConDataCons
  where
    pos :: Type -> Bool
    pos (FunTy t1 t2) = neg t1 && pos t2
    pos _ = True
    neg :: Type -> Bool
    neg (TyConApp _ _) = False -- Could this test whether the tycon is covariant?
    neg (TyVarTy _) = False
    neg (FunTy t1 t2) = pos t1 && neg t2
    neg _ = True

-- Check if a core datatype has one constructor
trivial :: TyCon -> Bool
trivial = (== 1) . length . tyConDataCons
