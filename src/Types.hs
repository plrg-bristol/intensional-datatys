{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Types (
  Type (..),
  Extended (..),
  Scheme (..),
  shape,
 
  applyTyVars,

  Fresh (E, inj),
  fromCore
) where

import Prelude hiding ((<>))

import Control.Monad.Identity
import Control.Monad.State

import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr
import Outputable

import Utils

-- Type level flags
data Extended where
  S    :: Extended -- Unrefined
  T    :: Extended -- Refined

data Scheme where
  M :: Scheme -- Monomorphic types
  P :: Scheme -- Polymorphic types

-- Generic representation of sort/type(scheme)
data Type (s :: Scheme) (e :: Extended) where
  Var     :: Core.Name -> Type s e
  App     :: Type M S -> Type M S -> Type s e

  Base    :: Core.TyCon -> Type s e
  Data    :: Core.TyCon -> Type s S
  Inj     :: Int -> Core.TyCon -> Type s T

  (:=>)   :: Type M e -> Type M e -> Type s e
  Lit     :: Tcr.TyLit -> Type s e

  Forall :: [Core.Name] -> Type M e -> Type P e

deriving instance Eq (Type s e)

-- TODO: Associate brackets
instance Outputable (Type s e) where
  ppr (Var a)       = ppr a
  ppr (App x y)     = ppr x <> ppr "@" <> ppr y
  ppr (Base b)      = ppr b
  ppr (Data d)      = ppr d
  ppr (Inj x d)     = ppr "inj" <> ppr x <> ppr " " <> ppr d
  ppr (x :=> y)     = ppr x <> ppr "->" <> ppr y
  ppr (Lit l)       = ppr l
  ppr (Forall as t) = ppr "forall" <> ppr as <> ppr "." <> ppr t

-- The underlying shape
shape :: Type s e -> Type s S
{-# INLINE shape #-}
shape (Var a)       = Var a
shape (App a b)     = App a b
shape (Base b)      = Base b
shape (Data d)      = Base d
shape (Inj _ d)     = Base d
shape (a :=> b)     = shape a :=> shape b
shape (Lit l)       = Lit l
shape (Forall as t) = Forall as (shape t)





-- Partially instantiate type scheme
applyTyVars :: Type P e -> [Type M e] -> Type P e
applyTyVars t [] = t
applyTyVars (Forall (a:as) u) (t:ts) = applyTyVars (Forall as (subTyVar a t u)) ts
  where
    subTyVar :: Core.Name -> Type M e -> Type M e -> Type M e
    subTyVar a (Var a') t 
      | a == a'    = t
      | otherwise  = Var a'
    subTyVar a (App x y) t = App (subTyVar a (shape t) x) (shape $ subTyVar a (shape t) y)
    subTyVar a (x :=> y) t = subTyVar a t x :=> subTyVar a t y
    subTyVar _ t _         = t
applyTyVars t ts = Core.pprPanic "Type scheme doesn't have that many type variables!" (Core.ppr (t, length ts))





-- Convert a core type
-- TODO: Specialise
fromCore :: (Quantified s, Fresh m) => Core.Type -> m (Type s (E m))
fromCore (Tcr.TyVarTy a) = return (Var $ Core.getName a)
fromCore (Tcr.AppTy t1 t2) = do
  s1 <- shape <$> fromCore t1
  s2 <- shape <$> fromCore t2
  return (App s1 s2)
fromCore (Tcr.TyConApp t args)
  | Core.isTypeSynonymTyCon t
  , Just (as, u) <- Core.synTyConDefn_maybe t
  = fromCore $ Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u
 
  | refinable t 
  = inj t

  | otherwise
  = return (Base t)
fromCore (Tcr.ForAllTy b t) = fromForAllTy b t 
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l) = return (Lit l)
fromCore t = Core.pprPanic "Unexpected Cast or Coercion type" (Core.ppr t)

-- How are datatypes handled?
class Monad m => Fresh m where
  type E m :: Extended 
  inj :: Core.TyCon -> m (Type s (E m))

instance Fresh Identity where
  type E Identity = S
  inj t = return (Data t)

-- How are quantifiers handled?
class Quantified s where
  fromForAllTy :: Fresh m => Core.TyVarBinder -> Core.Type -> m (Type s (E m))

instance Quantified M where
  fromForAllTy b t = Core.pprPanic "Unexpected quantifier in monomorphic type!" (Core.ppr (Tcr.ForAllTy b t))

instance Quantified P where
  fromForAllTy b t = do
    let a = Core.getName $ Core.binderVar b
    ss <- fromCore t
    return (Forall [a] ss)


