{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module DataTypes
  ( DataType (..),
    deepest,
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

-- Internal representation of datatypes
data DataType d where
  Level0 :: {underlying :: d} -> DataType d -- Top-level datatypes, e.g. singletons
  Level1 :: {underlying :: d} -> DataType d -- Full datatype
  Neutral :: {underlying :: d} -> DataType d
  deriving (Eq, Functor, Ord, Generic)

instance Hashable d => Hashable (DataType d)

instance Outputable d => Outputable (DataType d) where
  ppr (Level1 d) = char '\'' <> ppr d
  ppr dt = ppr $ underlying dt

instance Binary d => Binary (DataType d) where
  put_ bh (Level0 d) = put_ bh (0 :: Int) >> put_ bh d
  put_ bh (Level1 d) = put_ bh (1 :: Int) >> put_ bh d
  put_ bh (Neutral d) = put_ bh (2 :: Int) >> put_ bh d

  get bh = do
    l <- get bh
    case l :: Int of
      0 -> Level0 <$> get bh
      1 -> Level1 <$> get bh
      2 -> Neutral <$> get bh
      _ -> pprPanic "Binary is not a datatype!" (ppr l)

-- Inject a into the most unrolled level possible
deepest :: DataType a -> DataType b -> DataType a
deepest d (Level1 _) = Level1 (underlying d)
deepest (Neutral d) (Level0 _) = Level0 d
deepest d _ = d

-- Check if a core datatype is contravariant in every type argument
contravariant :: TyCon -> Bool
contravariant = any (not . pos) . concatMap dataConOrigArgTys . tyConDataCons
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
