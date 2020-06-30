{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE LambdaCase #-}

module Types
  ( RVar,
    Domain,
    Refined (..),
    DataType (..),
    trivial,
    Type,
    TypeGen (..),
    -- inj,
    decompType,
    subTyVar,
  )
where

import Binary
import Data.Bifunctor
import Data.Hashable
import qualified Data.IntSet as I
import GHC.Generics hiding (prec)
import GhcPlugins hiding ((<>), Expr (..), Type)
import IfaceType

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

instance Hashable d => Hashable (DataType d)

instance Outputable d => Outputable (DataType d) where
  ppr (Base d) = ppr d
  ppr (Inj x d) = hcat [text "inj_", ppr x] <+> ppr d

instance Binary d => Binary (DataType d) where
  put_ bh (Base d) = put_ bh False >> put_ bh d
  put_ bh (Inj x d) = put_ bh True >> put_ bh x >> put_ bh d
  get bh =
    get bh >>= \case
      False -> Base <$> get bh
      True -> Inj <$> get bh <*> get bh

instance Refined (DataType d) where
  domain (Base _) = I.empty
  domain (Inj x _) = I.singleton x

  rename x y (Inj z d)
    | x == z = Inj y d
  rename _ _ d = d

-- Check if a core datatype contains covariant arguments
-- covariant :: TyCon -> Bool
-- covariant = all pos . concatMap dataConOrigArgTys . tyConDataCons
--   where
--     pos, neg :: Type -> Bool
--     pos (FunTy t1 t2) = neg t1 && pos t2
--     pos _ = True
--     neg (FunTy t1 t2) = pos t1 && neg t2
--     neg (TyConApp _ _) = False -- These cases are overapproximate
--     neg (TyVarTy _) = False
--     neg _ = True

-- Check if a core datatype has only one constructor
trivial :: TyCon -> Bool
trivial = (<= 1) . length . tyConDataCons

type Type = TypeGen TyCon

-- Monomorphic types parameterised by type constructors
data TypeGen d
  = Var Name
  | App (TypeGen d) (TypeGen d)
  | Data (DataType d) [TypeGen d]
  | TypeGen d :=> TypeGen d
  | Lit IfaceTyLit
  | Ambiguous -- Ambiguous hides higher-ranked types and casts
  deriving (Functor, Foldable, Traversable)

-- Clone of a Outputable Core.Type
instance Outputable d => Outputable (TypeGen d) where
  ppr = pprTy topPrec
    where
      pprTy :: Outputable d => PprPrec -> TypeGen d -> SDoc
      pprTy _ (Var a) = ppr a
      pprTy prec (App t1 t2) = hang (pprTy prec t1) 2 (pprTy appPrec t2)
      pprTy _ (Data d as) = hang (ppr d) 2 $ sep [hcat [text "@", pprTy appPrec a] | a <- as]
      pprTy prec (t1 :=> t2) = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow, pprTy prec t2]
      pprTy _ (Lit l) = ppr l
      pprTy _ Ambiguous = text "<?>"

instance Binary d => Binary (TypeGen d) where
  put_ bh (Var a) = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b) = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Data d as) = put_ bh (2 :: Int) >> put_ bh d >> put_ bh as
  put_ bh (a :=> b) = put_ bh (3 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l) = put_ bh (4 :: Int) >> put_ bh l
  put_ bh Ambiguous = put_ bh (5 :: Int)

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> Var <$> get bh
      1 -> App <$> get bh <*> get bh
      2 -> Data <$> get bh <*> get bh
      3 -> (:=>) <$> get bh <*> get bh
      4 -> Lit <$> get bh
      5 -> return Ambiguous
      _ -> pprPanic "Invalid binary file!" $ ppr n

instance Refined (TypeGen d) where
  domain (App a b) = domain a <> domain b
  domain (Data d as) = domain d <> foldMap domain as
  domain (a :=> b) = domain a <> domain b
  domain _ = mempty

  rename x y (App a b) = App (rename x y a) (rename x y b)
  rename x y (Data d as) = Data (rename x y d) (rename x y <$> as)
  rename x y (a :=> b) = rename x y a :=> rename x y b
  rename _ _ t = t

-- Inject a sort into a refinement environment
-- inj :: Int -> TypeGen d -> TypeGen d
-- inj _ (Var a) = Var a
-- inj x (App a b) = App (inj x a) (inj x b)
-- inj x (Data (Base b) as) = Data (Base b) (inj x <$> as)
-- inj x (Data (Inj _ d) as) = Data (Inj x d) (inj x <$> as)
-- inj x (a :=> b) = inj x a :=> inj x b
-- inj _ (Lit l) = Lit l
-- inj _ Ambiguous = Ambiguous

-- Decompose a functions into its arguments and eventual return type
decompType :: TypeGen d -> ([TypeGen d], TypeGen d)
decompType (a :=> b) = first (++ [a]) (decompType b)
decompType a = ([], a)

-- Type variable substitution
subTyVar :: Outputable d => Name -> TypeGen d -> TypeGen d -> TypeGen d
subTyVar a t (Var a')
  | a == a' = t
  | otherwise = Var a'
subTyVar a t (App x y) = applyType (subTyVar a t x) (subTyVar a t y)
subTyVar a t (Data d as) = Data d (subTyVar a t <$> as)
subTyVar a t (x :=> y) = subTyVar a t x :=> subTyVar a t y
subTyVar _ _ t = t

-- Unsaturated type application
applyType :: Outputable d => TypeGen d -> TypeGen d -> TypeGen d
applyType (Var a) t = App (Var a) t
applyType (App a b) t = App (App a b) t
applyType (Data d as) t = Data d (as ++ [t])
applyType Ambiguous _ = Ambiguous
applyType a b = pprPanic "The type is already saturated!" $ ppr (a, b)
