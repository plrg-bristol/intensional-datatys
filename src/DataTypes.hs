{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}

module DataTypes
  ( RVar,
    Domain,
    Refined (..),
    DataType (..),
    trivial,
  )
where

import Binary
import Data.Hashable
import qualified Data.IntSet as I
import GHC.Generics
import GhcPlugins

type RVar = Int

type Domain = I.IntSet

-- The class of objects containing refinement variables
class Refined t where
  domain :: t -> Domain
  rename :: RVar -> RVar -> t -> t

-- A datatype identifier
-- d is TyCon, IfaceTyCon or Name
data DataType d
  = Base d
  | Inj RVar d -- Extended datatypes from the canonical environment
  deriving (Eq, Functor, Foldable, Generic, Traversable)

instance Binary d => Binary (DataType d) where
  put_ bh (Base d) = put_ bh False >> put_ bh d
  put_ bh (Inj x d) = put_ bh True >> put_ bh x >> put_ bh d
  get bh =
    get bh >>= \case
      False -> Base <$> get bh
      True -> Inj <$> get bh <*> get bh

instance Hashable d => Hashable (DataType d)

instance Outputable d => Outputable (DataType d) where
  ppr (Base d) = ppr d
  ppr (Inj x d) = hcat [text "inj_", ppr x] <+> ppr d

instance Refined (DataType d) where
  domain (Base _) = I.empty
  domain (Inj x _) = I.singleton x

  rename x y (Inj z d)
    | x == z = Inj y d
  rename _ _ d = d

-- Check if a core datatype has only one constructor
trivial :: TyCon -> Bool
trivial = (== 1) . length . tyConDataCons
-- Check if a core datatype is covariant in every type argument
-- covariant :: TyCon -> Bool
-- covariant = all pos . concatMap dataConOrigArgTys . tyConDataCons
--   where
--     pos, neg :: Type -> Bool
--     pos (FunTy t1 t2) = neg t1 && pos t2
--     pos _ = True
--     neg (TyConApp _ _) = False -- This is an overapproximation
--     neg (TyVarTy _) = False
--     neg (FunTy t1 t2) = pos t1 && neg t2
--     neg _ = True

-- underlying :: DataType d -> d
-- underlying (Base b) = b
-- underlying (Inj _ d) = d
