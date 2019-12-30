{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}

module Types (
  Type (..),
  Extended (..),
  Scheme(..),
  pattern Forall,
  shape,
  inj,
  mono,

  Rename(..),

  FromCore (..),
  fromCore,
  applyTyVars
) where

import Prelude hiding ((<>))

import Control.Monad.Trans.Identity

import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr
import Outputable

import Utils

-- Type level flags
data Extended where
  S    :: Extended -- Unrefined
  T    :: Extended -- Refined

-- Interal representation of sorts, types and schemes
data Type (e :: Extended) where
  Var    :: Core.Name -> Type e
  App    :: Type S -> Type S -> Type e
  Base   :: Core.TyCon -> Type e
  Data   :: Core.TyCon -> Type S
  Inj    :: Int -> Core.TyCon -> Type T
  (:=>)  :: Type e -> Type e -> Type e
  Lit    :: Tcr.TyLit -> Type e

deriving instance Eq (Type e)

-- TODO: Associate brackets
instance Outputable (Type e) where
  ppr (Var a)       = ppr a
  ppr (App x y)     = ppr x <> ppr "@" <> ppr y
  ppr (Base b)      = ppr b
  ppr (Data d)      = ppr d
  ppr (Inj x d)     = ppr "inj" <> ppr x <> ppr " " <> ppr d
  ppr (x :=> y)     = ppr x <> ppr "->" <> ppr y
  ppr (Lit l)       = ppr l

-- Typescheme
newtype Scheme (e :: Extended) = Scheme ([Core.Name], Type e)

pattern Forall :: [Core.Name] -> Type e -> Scheme e
pattern Forall as u = Scheme (as, u)

instance Outputable (Scheme e) where
  ppr (Forall as u) = ppr "forall" <> ppr as <> ppr "." <> ppr u 

-- The underlying shape
shape :: Type e -> Type S
{-# INLINE shape #-}
shape (Var a)       = Var a
shape (App a b)     = App a b
shape (Base b)      = Base b
shape (Data d)      = Base d
shape (Inj _ d)     = Base d
shape (a :=> b)     = shape a :=> shape b
shape (Lit l)       = Lit l

-- Inject any sort
inj :: Int -> Type e -> Type T
{-# INLINE inj #-}
inj x (Var a) = Var a
inj x (App a b) = App a b
inj x (Base b) = Base b
inj x (Data d) = Inj x d
inj x (Inj _ d) = Inj x d
inj x (a :=> b) = inj x a :=> inj x b
inj x (Lit l) = Lit l

-- Demand that a typescheme is fully instantiated
mono :: Scheme e -> Type e
mono (Forall [] t) = t
mono (Forall as t) = Core.pprPanic "Type scheme must be fully istantiated!" (Core.ppr (as, t))

-- Replace refinement variables
-- TODO: Specialise
class Rename t where
  rename :: Int -> Int -> t -> t

instance Rename (Type s) where
  rename x y (Var a) = Var a
  rename x y (App a b) = App (rename x y a) (rename x y b)
  rename x y (Base b) = Base b
  rename x y (Data d) = Data d
  rename x y (Inj x' d)
    | x == x'   = Inj y d
    | otherwise = Inj x' d
  rename x y (a :=> b) = rename x y a :=> rename x y b
  rename x y (Lit l) = Lit l

instance Rename (Scheme s) where
  rename x y (Forall as t) = Forall as $ rename x y t

-- Convert from a core type
-- TODO: Specialise
class FromCore (e :: Extended) where
  type M e :: (* -> *) -> * -> *
  dataType :: Monad m => Core.TyCon -> M e m (Scheme e)

instance FromCore S where
  type M S = IdentityT
  dataType t = return $ Forall [] (Data t)

fromCore :: (Monad m, Monad (M e m), FromCore e) => Core.Type -> M e m (Scheme e)
fromCore (Tcr.TyVarTy a) = return $ Forall [] (Var $ Core.getName a)
fromCore (Tcr.AppTy t1 t2) = do
  s1 <- runIdentityT $ fromCore t1
  s2 <- runIdentityT $ fromCore t2
  return $ Forall [] (App (mono s1) (mono s2))
fromCore (Tcr.TyConApp t args)
  | Core.isTypeSynonymTyCon t
  , Just (as, u) <- Core.synTyConDefn_maybe t
  = fromCore (Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u)
 
  | refinable t 
  = dataType t

  | otherwise
  = return $ Forall [] (Base t)
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ Forall [] (mono s1 :=> mono s2)
fromCore (Tcr.LitTy l) = return $ Forall [] (Lit l)
fromCore (Tcr.ForAllTy b t) = Core.pprPanic "Unexpected quantifier in core type!" (Core.ppr ())
fromCore t = Core.pprPanic "Unexpected Cast or Coercion type" (Core.ppr t)

-- Partially instantiate type scheme
applyTyVars :: (FromCore e, Monad (M e m), Monad m) => Scheme e -> Core.Type -> M e m (Scheme e)
applyTyVars (Forall (a:as) u) t = do
  u' <- subTyVar a u t
  return $ Forall as u'
  where
    subTyVar :: (FromCore e, Monad (M e m), Monad m) => Core.Name -> Type e -> Core.Type -> M e m (Type e)
    subTyVar a (Var a') t 
      | a == a'    = mono <$> fromCore t
      | otherwise  = return (Var a')
    subTyVar a (App x y) t = do
      x' <- runIdentityT $ subTyVar a x t
      y' <- runIdentityT $ subTyVar a y t
      return $ App x' y' 
    subTyVar a (x :=> y) t = do
      x' <- subTyVar a x t
      y' <- subTyVar a y t
      return (x :=> y)
    subTyVar _ t _ = return t 
applyTyVars t _ = Core.pprPanic "Type scheme doesn't have that many type variables!" (Core.ppr t)
