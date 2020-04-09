{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Types (
  DataType(..),

  Extended(..),
  Type(..),
  inj,
  shape,
  applyType,
  subTyVar,
  decomp,
  unroll,

  Refined(..),
) where

import Prelude hiding ((<>), sum, max)
import qualified Data.List as L

import Name
import TyCon
import Binary
import ToIface
import IfaceType
import BasicTypes
import Outputable

-- Unrefined sorts vs refined types
data Extended = S | T

-- Monomorphic types
type DataType d = (Bool, d) -- Unrolled?
data Type (e :: Extended) d where
  Var    :: Name -> Type e d
  App    :: Type S d -> Type S d -> Type e d
  Base   :: d -> [Type S d] -> Type e d
  Inj    :: Int -> DataType d -> [Type S d] -> Type T d
  (:=>)  :: Type e d -> Type e d -> Type e d
  Lit    :: IfaceTyLit -> Type e d

  -- Ambiguous hides higher-ranked types and casts
  Ambiguous :: Type e d

deriving instance Functor (Type e)

-- Compare type shapes
instance Eq d => Eq (Type S d) where
  Ambiguous == _         = True
  _ == Ambiguous         = True
  Var _ == Var _         = True
  App f a == App g b     = f == g && a == b
  Base f a == Base g b   = f == g && a == b
  (a :=> b) == (c :=> d) = a == c && b == d
  Lit l == Lit l'        = l == l'
  _ == _                 = False

-- Clone of a Outputable Core.Type
instance Outputable d => Outputable (Type e d) where
  ppr = pprTy topPrec
    where
      pprTy :: Outputable d => PprPrec -> Type e d -> SDoc
      pprTy _ (Var a)         = ppr a
      pprTy prec (App t1 t2)  = hang (pprTy prec t1)
                                   2 (pprTy appPrec t2)
      pprTy _ (Base b as)     = hang (ppr b)
                                   2 (sep $ fmap ((text "@" <>) . pprTy appPrec) as)
      pprTy prec (Inj x d as) = hang (maybeParen prec appPrec $ sep [text "inj", ppr x, ppr d])
                                   2 (sep $ fmap ((text "@" <>) . pprTy appPrec) as)
      pprTy prec (t1 :=> t2)  = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l)         = ppr l
      pprTy _ Ambiguous       = unicodeSyntax (char '□') (text "ambiguous")

instance Binary (Type T IfaceTyCon) where
  put_ bh (Var a)      = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b)    = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Base b as)  = put_ bh (2 :: Int) >> put_ bh b >> put_ bh as
  put_ bh (Inj x d as) = put_ bh (3 :: Int) >> put_ bh x >> put_ bh d >> put_ bh as
  put_ bh (a :=> b)    = put_ bh (4 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l)      = put_ bh (5 :: Int) >> put_ bh l
  put_ bh Ambiguous    = put_ bh (6 :: Int)

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
      _ -> pprPanic "Invalid binary file!" $ ppr ()

instance Binary (Type S IfaceTyCon) where
  put_ bh (Var a)      = put_ bh (0 :: Int) >> put_ bh a
  put_ bh (App a b)    = put_ bh (1 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Base b as)  = put_ bh (2 :: Int) >> put_ bh b >> put_ bh as
  put_ bh (a :=> b)    = put_ bh (3 :: Int) >> put_ bh a >> put_ bh b
  put_ bh (Lit l)      = put_ bh (4 :: Int) >> put_ bh l
  put_ bh Ambiguous    = put_ bh (5 :: Int)

  get bh = do
    n <- get bh
    case n :: Int of
      0 -> Var <$> get bh
      1 -> App <$> get bh <*> get bh
      2 -> Base <$> get bh <*> get bh
      3 -> (:=>) <$> get bh <*> get bh
      4 -> Lit <$> get bh
      5 -> return Ambiguous
      _ -> pprPanic "Invalid binary file!" $ ppr ()

instance Binary (Type e IfaceTyCon) => Binary (Type e TyCon) where
  put_ bh = put_ bh . fmap toIfaceTyCon
  get bh  = pprPanic "Cannot write non-interface types to file" $ ppr ()

-- Inject a sort into a refinement environment
inj :: Int -> Type e d -> Type T d
inj _ (Var a)       = Var a
inj _ (App a b)     = App a b
inj _ (Base b as)   = Base b as
inj x (Inj _ d as)  = Inj x d as
inj x (a :=> b)     = inj x a :=> inj x b
inj _ (Lit l)       = Lit l
inj _ Ambiguous     = Ambiguous

-- The shape of a type
shape :: Type e d -> Type S d
shape (Var a)           = Var a
shape (App a b)         = App (shape a) (shape b)
shape (Base b as)       = Base b (shape <$> as)
shape (Inj _ (_, d) as) = Base d (shape <$> as)
shape (a :=> b)         = shape a :=> shape b
shape (Lit l)           = Lit l
shape Ambiguous         = Ambiguous

-- Type application
applyType :: Outputable d => Type e d -> Type e d -> Type e d
applyType Ambiguous    _ = Ambiguous
applyType (Base b as)  t = Base b (as ++ [shape t])
applyType (Inj x d as) t = Inj x d (as ++ [shape t])
applyType (Var a)      t = App (Var a) (shape t)
applyType (App a b)    t = App (App a b) (shape t)
applyType t t'           = pprPanic "The type is saturated!" $ ppr (t, t')

-- Type variable substitution
subTyVar :: Outputable d => Name -> Type e d -> Type e d -> Type e d
subTyVar a t (Var a')
  | a == a'    = t
  | otherwise  = Var a'
subTyVar a t (App x y) =
  case applyType (subTyVar a (shape t) x) $ subTyVar a (shape t) y of
    Base b as -> Base b as
    Var a     -> Var a
    App a b   -> App a b
    _         -> pprPanic "Invalid application in types!" $ ppr (x, y)
subTyVar a t (x :=> y)    = subTyVar a t x :=> subTyVar a t y
subTyVar a t (Base b as)  = Base b (subTyVar a (shape t) <$> as)
subTyVar a t (Inj x d as) = Inj x d (subTyVar a (shape t) <$> as)
subTyVar _ _ t            = t

-- Decompose a function type into arguments and eventual return type
decomp :: Type T d -> ([Type T d], Type T d)
decomp (a :=> b) = let (as, r) = decomp b in (a:as, r)
decomp t         = ([], t)

-- Unroll a datatype
unroll :: Eq d => d -> Type T d -> Type T d
unroll d (Inj x (b, d') as) = Inj x (b || d == d', d') as
unroll d (a :=> b)          = unroll d a :=> unroll d b
unroll d t                  = t

-- Objects that are parameterised by refinement variables
class Refined t where
  freevs :: t -> [Int]
  rename :: Int -> Int -> t -> t

instance Refined Name where
  freevs _   = []
  rename _ _ = id

instance Refined (DataType Name) where
  freevs _   = []
  rename _ _ = id

instance Refined (Type T d) where
  freevs (Inj x _ as) = [x]
  freevs (a :=> b)    = freevs a `L.union` freevs b
  freevs _            = []

  rename x y (Inj x' d as)
    | x == x'           = Inj y d as
    | otherwise         = Inj x' d as
  rename x y (a :=> b)  = rename x y a :=> rename x y b
  rename _ _ t          = t
