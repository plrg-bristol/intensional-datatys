{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}

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
import GhcPlugins
import TyCoRep
import Prelude hiding ((<>))

data Level
  = Initial -- Singletons or Non-empty etc
  | Full -- Infinite or Empty
  deriving (Eq, Generic)

instance Hashable Level

instance Binary Level where
  put_ bh Initial = put_ bh False
  put_ bh Full = put_ bh True

  get bh =
    get bh >>= \case
      False -> return Initial
      True -> return Full

instance Outputable Level where
  ppr Initial = char '\''
  ppr Full = empty

-- Internal representation of datatypes
data DataType d
  = DataType
      { level :: Level,
        orig :: d
      }
  deriving (Eq, Functor, Foldable, Traversable, Generic)

instance Hashable d => Hashable (DataType d)

instance Outputable d => Outputable (DataType d) where
  ppr d
    | level d == Initial = char '\'' <> ppr (orig d)
    | otherwise = ppr (orig d)

instance Binary d => Binary (DataType d) where
  put_ bh (DataType l d) = put_ bh l >> put_ bh d

  get bh = DataType <$> get bh <*> get bh

-- Check if a core datatype is contravariant in every type argument
contravariant :: TyCon -> Bool
contravariant = not . all pos . concatMap dataConOrigArgTys . tyConDataCons
  where
    pos, neg :: Type -> Bool
    pos (FunTy t1 t2) = neg t1 && pos t2
    pos _ = True
    neg (TyConApp _ _) = False -- ? Could this test whether the tycon is covariant
    neg (TyVarTy _) = False
    neg (FunTy t1 t2) = pos t1 && neg t2
    neg _ = True

-- Check if a core datatype has one constructor
trivial :: TyCon -> Bool
trivial = (== 1) . length . tyConDataCons
