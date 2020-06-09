{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module Types
  ( RVar,
    Domain,
    Refined (..),
    Extended (..),
    Type,
    IfType,
    TypeGen (..),
    inj,
    shape,
    applyType,
    subTyVar,
    decompTy,
    increaseLevel,
  )
where

import Binary
import qualified Data.IntSet as I
import DataTypes
import GhcPlugins hiding (Expr (..), Type)
import IfaceType
import Prelude hiding ((<>))

-- Refinement variable
type RVar = Int

type Domain = I.IntSet

-- The class of objects that contain refinement variables
class Refined t where
  domain :: t -> Domain
  rename :: RVar -> RVar -> t -> t

--  It is necessary to distinguish unrefined sorts vs refined types
--  Only sorts can appear as arguments to type constructors for three reasons:
--  a) our constraint language doesn't contain type variables
--  b) we can't construct a slice of a type variable
--  c) modules that haven't been processed must have their types "maximised";
--     we would, therefore, need to abstractly guard constraints by the presence of constructors which are co- and contravariant w.r.t this variable
--
--  This is distinct from Base types which represent both:
--  a) datatypes with contravariant constructors (when the contra flag is off)
--  b) datatypes with only one constructor
data Extended = S | T

-- Monomorphic types
type Type e = TypeGen e TyCon

type IfType e = TypeGen e IfaceTyCon

data TypeGen (e :: Extended) d where
  Var :: Name -> TypeGen e d
  App :: TypeGen e d -> TypeGen 'S d -> TypeGen e d
  Base :: d -> [TypeGen 'S d] -> TypeGen e d
  Data :: DataType d -> [TypeGen 'S d] -> TypeGen 'S d
  Inj :: RVar -> DataType d -> [TypeGen 'S d] -> TypeGen 'T d
  (:=>) :: TypeGen e d -> TypeGen e d -> TypeGen e d
  Lit :: IfaceTyLit -> TypeGen e d
  -- Ambiguous hides higher-ranked types and casts
  Ambiguous :: TypeGen d e

-- Compare type shapes
instance Eq (Type 'S) where
  Ambiguous == _ = True
  _ == Ambiguous = True
  Var _ == Var _ = True
  App f a == App g b = f == g && a == b
  Base f a == Base g b = f == g && a == b
  Data f a == Data g b = orig f == orig g && a == b
  Data f a == Base g b = orig f == g && a == b
  Base f a == Data g b = orig g == f && a == b
  (a :=> b) == (c :=> d) = a == c && b == d
  Lit l == Lit l' = l == l'
  _ == _ = False

-- Clone of a Outputable Core.Type
instance Outputable d => Outputable (TypeGen e d) where
  ppr = pprTy topPrec
    where
      pprTy :: Outputable d => PprPrec -> TypeGen e d -> SDoc
      pprTy _ (Var a) = ppr a
      pprTy prec (App t1 t2) =
        hang
          (pprTy prec t1)
          2
          (pprTy appPrec t2)
      pprTy _ (Base b as) = withArgs (ppr b) as
      pprTy _ (Data d as) = withArgs (ppr d) as
      pprTy prec (Inj x d as) =
        withArgs
          (maybeParen prec appPrec $ sep [text "inj", ppr x, ppr d])
          as
      pprTy prec (t1 :=> t2) = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l) = ppr l
      pprTy _ Ambiguous = unicodeSyntax (char '□') (text "ambiguous")
      withArgs :: Outputable d => SDoc -> [TypeGen e d] -> SDoc
      withArgs d as =
        hang d 2 (sep $ fmap ((text "@" <>) . pprTy appPrec) as)

instance Binary (IfType 'T) where
  put_ bh (Var a) = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b) = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Base b as) = put_ bh (2 :: Int) >> put_ bh b >> put_ bh as
  put_ bh (Inj x d as) = put_ bh (3 :: Int) >> put_ bh x >> put_ bh d >> put_ bh as
  put_ bh (a :=> b) = put_ bh (4 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l) = put_ bh (5 :: Int) >> put_ bh l
  put_ bh Ambiguous = put_ bh (6 :: Int)

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> Var <$> get bh
      1 -> App <$> get bh <*> get bh
      2 -> Base <$> get bh <*> get bh
      3 -> Inj <$> get bh <*> get bh <*> get bh
      4 -> (:=>) <$> get bh <*> get bh
      5 -> Lit <$> get bh
      6 -> return Ambiguous
      _ -> pprPanic "Invalid binary file!" $ ppr n

instance Binary (IfType 'S) where
  put_ bh (Var a) = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b) = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Base b as) = put_ bh (2 :: Int) >> put_ bh b >> put_ bh as
  put_ bh (Data b as) = put_ bh (3 :: Int) >> put_ bh b >> put_ bh as
  put_ bh (a :=> b) = put_ bh (4 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l) = put_ bh (5 :: Int) >> put_ bh l
  put_ bh Ambiguous = put_ bh (6 :: Int)

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> Var <$> get bh
      1 -> App <$> get bh <*> get bh
      2 -> Base <$> get bh <*> get bh
      3 -> Data <$> get bh <*> get bh
      4 -> (:=>) <$> get bh <*> get bh
      5 -> Lit <$> get bh
      6 -> return Ambiguous
      _ -> pprPanic "Invalid binary file!" $ ppr ()

instance Refined (TypeGen 'T d) where
  domain (Inj x _ _) = I.singleton x
  domain (a :=> b) = I.union (domain a) (domain b)
  domain _ = I.empty

  rename x y (Inj x' d as)
    | x == x' = Inj y d as
    | otherwise = Inj x' d as
  rename x y (a :=> b) = rename x y a :=> rename x y b
  rename _ _ t = t

-- Inject a sort into a refinement environment
inj :: RVar -> Type e -> Type 'T
inj _ (Var a) = Var a
inj x (App a b) = App (inj x a) b
inj _ (Base d as) = Base d as
inj x (Data d as) = Inj x d as
inj x (Inj _ d as) = Inj x d as
inj x (a :=> b) = inj x a :=> inj x b
inj _ (Lit l) = Lit l
inj _ Ambiguous = Ambiguous

-- The shape of a type
shape :: Type e -> Type 'S
shape (Var a) = Var a
shape (App a b) = App (shape a) b
shape (Base d as) = Base d as
shape (Data d as) = Data d as
shape (Inj _ d as) = Data d as
shape (a :=> b) = shape a :=> shape b
shape (Lit l) = Lit l
shape Ambiguous = Ambiguous

-- Type application
applyType :: Type e -> Type 'S -> Type e
applyType Ambiguous _ = Ambiguous
applyType (Base b as) t = Base b (as ++ [t])
applyType (Data b as) t = Data b (as ++ [t])
applyType (Inj x d as) t = Inj x d (as ++ [t])
applyType (Var a) t = App (Var a) t
applyType (App a b) t = App (App a b) t
applyType t t' = pprPanic "The type is saturated!" $ ppr (t, t')

-- Type variable substitution
subTyVar :: Name -> Type e -> Type e -> Type e
subTyVar a t (Var a')
  | a == a' = t
  | otherwise = Var a'
subTyVar a t (App x y) = applyType (subTyVar a t x) $ subTyVar a (shape t) y
subTyVar a t (x :=> y) = subTyVar a t x :=> subTyVar a t y
subTyVar a t (Base b as) = Base b (subTyVar a (shape t) <$> as)
subTyVar a t (Data b as) = Data b (subTyVar a t <$> as)
subTyVar a t (Inj x d as) = Inj x d (subTyVar a (shape t) <$> as)
subTyVar _ _ t = t

-- Decompose a functions into its arguments and eventual return type
decompTy :: Type e -> ([Type e], Type e)
decompTy (a :=> b) =
  let (as, r) = decompTy b
   in (as ++ [a], r)
decompTy t = ([], t)

-- Unroll a datatype when it is "under" itself
increaseLevel :: TyCon -> Type e -> Type e
increaseLevel d (Data d' as)
  | d == orig d' = Data d' {level = Full} (increaseLevel d <$> as)
increaseLevel d (Base d' as) = Base d' (increaseLevel d <$> as)
increaseLevel d (Inj x d' as)
  | d == orig d' = Inj x d' {level = Full} (increaseLevel d <$> as)
increaseLevel d (t :=> t') = increaseLevel d t :=> increaseLevel d t'
increaseLevel d (App a b) = App (increaseLevel d a) (increaseLevel d b)
increaseLevel _ t = t
