{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}

module Types
  ( RVar,
    Refined (..),
    Extended (..),
    Type (..),
    inj,
    shape,
    applyType,
    subTyVar,
    decompTy,
    unrollUnder,
    promoteTy,
  )
where

import Binary
import Control.Monad
import Data.Functor.Identity
import qualified Data.List as L
import DataTypes
import GhcPlugins hiding (Expr (..), Type)
import IfaceType
import ToIface
import qualified TyCoRep as Tcr
import Prelude hiding ((<>))

-- Refinement variable
type RVar = Int

-- The class of objects that contain refinement variables
class Refined t m where
  domain :: t -> m [RVar]
  rename :: RVar -> RVar -> t -> m t

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
data Type (e :: Extended) d where
  Var :: Name -> Type e d
  App :: Type e d -> Type S d -> Type e d
  Base :: d -> [Type S d] -> Type e d
  Data :: DataType d -> [Type S d] -> Type S d
  Inj :: RVar -> DataType d -> [Type S d] -> Type T d
  (:=>) :: Type e d -> Type e d -> Type e d
  Lit :: IfaceTyLit -> Type e d
  -- Ambiguous hides higher-ranked types and casts
  Ambiguous :: Type e d

deriving instance Functor (Type e)

-- Compare type shapes
instance Eq d => Eq (Type S d) where
  Ambiguous == _ = True
  _ == Ambiguous = True
  Var _ == Var _ = True
  App f a == App g b = f == g && a == b
  Base f a == Base g b = f == g && a == b
  Data f a == Data g b = underlying f == underlying g && a == b
  Data f a == Base g b = underlying f == g && a == b
  Base f a == Data g b = underlying g == f && a == b
  (a :=> b) == (c :=> d) = a == c && b == d
  Lit l == Lit l' = l == l'
  _ == _ = False

-- Clone of a Outputable Core.Type
instance Outputable d => Outputable (Type e d) where
  ppr = pprTy topPrec
    where
      pprTy :: Outputable d => PprPrec -> Type e d -> SDoc
      pprTy _ (Var a) = ppr a
      pprTy prec (App t1 t2) =
        hang
          (pprTy prec t1)
          2
          (pprTy appPrec t2)
      pprTy _ (Base b as) =
        hang
          (ppr b)
          2
          (sep $ fmap ((text "@" <>) . pprTy appPrec) as)
      pprTy _ (Data b as) =
        hang
          (ppr b)
          2
          (sep $ fmap ((text "@" <>) . pprTy appPrec) as)
      pprTy prec (Inj x d as) =
        hang
          (maybeParen prec appPrec $ sep [text "inj", ppr x, ppr d])
          2
          (sep $ fmap ((text "@" <>) . pprTy appPrec) as)
      pprTy prec (t1 :=> t2) = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l) = ppr l
      pprTy _ Ambiguous = unicodeSyntax (char '□') (text "ambiguous")

instance Binary (Type T IfaceTyCon) where
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

instance Binary (Type S IfaceTyCon) where
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

instance Binary (Type e IfaceTyCon) => Binary (Type e TyCon) where
  put_ bh = put_ bh . fmap toIfaceTyCon
  get _ = pprPanic "Cannot write non-interface types to file" $ ppr ()

instance Refined (Type T d) Identity where
  domain (Inj x _ as) = return [x]
  domain (a :=> b) = liftM2 L.union (domain a) (domain b)
  domain _ = return []

  rename x y (Inj x' d as)
    | x == x' = return (Inj y d as)
    | otherwise = return (Inj x' d as)
  rename x y (a :=> b) = liftM2 (:=>) (rename x y a) (rename x y b)
  rename _ _ t = return t

-- Inject a sort into a refinement environment
inj :: RVar -> Type e d -> Type T d
inj _ (Var a) = Var a
inj x (App a b) = App (inj x a) b
inj _ (Base d as) = Base d as
inj x (Data d as) = Inj x d as
inj x (Inj _ d as) = Inj x d as
inj x (a :=> b) = inj x a :=> inj x b
inj _ (Lit l) = Lit l
inj _ Ambiguous = Ambiguous

-- The shape of a type
shape :: Type e d -> Type S d
shape (Var a) = Var a
shape (App a b) = App (shape a) b
shape (Base d as) = Base d as
shape (Data d as) = Data d as
shape (Inj _ d as) = Data d as
shape (a :=> b) = shape a :=> shape b
shape (Lit l) = Lit l
shape Ambiguous = Ambiguous

-- Type application
applyType :: Outputable d => Type e d -> Type S d -> Type e d
applyType Ambiguous _ = Ambiguous
applyType (Base b as) t = Base b (as ++ [t])
applyType (Data b as) t = Data b (as ++ [t])
applyType (Inj x d as) t = Inj x d (as ++ [t])
applyType (Var a) t = App (Var a) t
applyType (App a b) t = App (App a b) t
applyType t t' = pprPanic "The type is saturated!" $ ppr (t, t')

-- Type variable substitution
subTyVar :: Outputable d => Name -> Type e d -> Type e d -> Type e d
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
decompTy :: Type e d -> ([Type e d], Type e d)
decompTy (a :=> b) =
  let (as, r) = decompTy b
   in (as ++ [a], r)
decompTy t = ([], t)

-- Unroll a datatype when it is "under" itself
unrollUnder :: Eq d => d -> Type e d -> Type e d
unrollUnder d (Data d' as)
  | d == underlying d' = Data (Level1 d) (unrollUnder d <$> as)
unrollUnder d (Base d' as) = Base d' (unrollUnder d <$> as)
unrollUnder d (Inj x d' as)
  | d == underlying d' = Inj x (Level1 d) (unrollUnder d <$> as)
unrollUnder d (t :=> t') = unrollUnder d t :=> unrollUnder d t'
unrollUnder d (App a b) = App (unrollUnder d a) (unrollUnder d b)
unrollUnder _ t = t

-- Lift a iface type to a full type
promoteTy :: Tcr.Type -> Type e IfaceTyCon -> Type e TyCon
promoteTy (Tcr.TyConApp tc args) t
  | isTypeSynonymTyCon tc, -- Type synonym
    Just (as, s) <- synTyConDefn_maybe tc =
    promoteTy (substTy (extendTvSubstList emptySubst (zip as args)) s) t
promoteTy _ (Var a) = Var a
promoteTy (Tcr.AppTy a' b') (App a b) = App (promoteTy a' a) (promoteTy b' b)
promoteTy (Tcr.TyConApp tc as') (Data d as) = Data (tc <$ d) (uncurry promoteTy <$> zip as' as)
promoteTy (Tcr.TyConApp tc as') (Inj x d as) = Inj x (tc <$ d) (uncurry promoteTy <$> zip as' as)
promoteTy (Tcr.TyConApp tc as') (Base d as) = Base tc (uncurry promoteTy <$> zip as' as)
promoteTy (Tcr.FunTy a' b') (a :=> b) = promoteTy a' a :=> promoteTy b' b
promoteTy _ (Lit l) = Lit l
promoteTy _ Ambiguous = Ambiguous
promoteTy t i = pprPanic "Interface type does not align with term type!" $ ppr (t, i)
