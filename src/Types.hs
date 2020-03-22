{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Types (
  Extended(..),
  Type(..),

  inj,
  shape,
  decomp,
  result,

  Refined(..)
) where

import Prelude hiding ((<>))
import qualified Data.Set as S

import Name
import IfaceType
import BasicTypes
import Outputable

data Extended where
  S :: Extended -- Unrefined
  T :: Extended -- Refined

-- Monomorphic types
data Type (e :: Extended) d where
  Var    :: Name -> Type e d
  App    :: Type S d -> Type S d -> Type e d
  Base   :: d -> [Type S d] -> Type e d
  Data   :: d -> [Type S d] -> Type S d
  Inj    :: Int -> d -> [Type T d] -> Type T d
  (:=>)  :: Type e d -> Type e d -> Type e d
  Lit    :: IfaceTyLit -> Type e d

  -- Ambiguous hides higher-ranked types and casts
  Ambiguous :: Type e d

deriving instance Eq d => Eq (Type e d)
deriving instance Functor (Type e)

-- Clone of a Outputable (Core.Type)
instance Outputable d => Outputable (Type e d) where
  ppr = pprTy topPrec
    where
      pprTy :: Outputable d => PprPrec -> Type e d -> SDoc
      pprTy _ (Var a)         = ppr a
      pprTy prec (App t1 t2)  = hang (pprTy prec t1)
                                   2 (pprTy appPrec t2)
      pprTy _ (Base b as)     = hang (ppr b)
                                   2 (sep $ fmap (\a -> text "@" <> pprTy appPrec a) as)
      pprTy _ (Data d as)     = hang (ppr d)
                                   2 (sep $ fmap (\a -> text "@" <> pprTy appPrec a) as)
      pprTy prec (Inj x d as) = hang (maybeParen prec appPrec $ sep [text "inj", ppr x, ppr d])
                                   2 (sep $ fmap (\a -> text "@" <> pprTy appPrec a) as)
      pprTy prec (t1 :=> t2)  = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l)         = ppr l
      pprTy _ Ambiguous       = unicodeSyntax (char '□') (text "ambiguous")

-- Inject a sort into a refinement environment
inj :: Int -> Type e d -> Type T d
inj _ (Var a)       = Var a
inj _ (App a b)     = App a b
inj _ (Base b as)   = Base b as
inj x (Data d as)   = Inj x d (inj x <$> as)
inj x (Inj _ d as)  = Inj x d (inj x <$> as)
inj x (a :=> b)     = inj x a :=> inj x b
inj _ (Lit l)       = Lit l
inj _ Ambiguous     = Ambiguous

-- The shape of a type
shape :: Type e d -> Type S d
shape (Var a)       = Var a
shape (App a b)     = App (shape a) (shape b)
shape (Base b as)   = Base b (shape <$> as)
shape (Data d as)   = Base d (shape <$> as)
shape (Inj _ d as)  = Base d (shape <$> as)
shape (a :=> b)     = shape a :=> shape b
shape (Lit l)       = Lit l
shape Ambiguous     = Ambiguous

-- Decompose a function type into arguments and eventual return type
decomp :: Type T d -> ([Type T d], Type T d)
decomp (a :=> b) = let (as, r) = decomp b in (a:as, r)
decomp t         = ([], t)

-- Extract the result type of a function
result :: Type T d -> Type T d
result = snd . decomp

-- Objects that are parameterised by refinement variables
class Refined t where
  domain :: t -> S.Set Int
  rename :: Int -> Int -> t -> t

instance Refined () where
  domain _   = S.empty
  rename _ _ = id

instance Refined Name where
  domain _    = S.empty
  rename _ _ = id

instance Refined (Type T d) where
  domain (Inj x _ as) = foldr (S.union . domain) (S.singleton x) as
  domain (a :=> b)    = S.union (domain a) (domain b)
  domain _            = S.empty

  rename x y (Inj x' d as)
    | x == x'           = Inj y d (rename x y <$> as)
    | otherwise         = Inj x' d (rename x y <$> as)
  rename x y (a :=> b)  = rename x y a :=> rename x y b
  rename _ _ t          = t
