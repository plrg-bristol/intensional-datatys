{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}

module Types (
  Type (..),
  Extended (..),
  shape,
  inj,

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
  S :: Extended -- Unrefined
  T :: Extended -- Refined

data Type (e :: Extended) where
  Var    :: Core.Name -> Type e
  App    :: Type S -> Type S -> Type e
  Base   :: Core.TyCon -> Type e
  Data   :: Core.TyCon -> Type S
  Inj    :: Int -> Core.TyCon -> Type T
  (:=>)  :: Type e -> Type e -> Type e
  Lit    :: Tcr.TyLit -> Type e
  Forall :: Core.Name -> Type e -> Type e

deriving instance Eq (Type e)

-- TODO: Associate brackets
instance Outputable (Type e) where
  ppr (Var a)       = ppr a
  ppr (App x y)     = ppr x <> ppr "@" <> ppr y
  ppr (Base b)      = ppr b
  ppr (Data d)      = ppr d
  ppr (Inj x d)     = ppr "inj" <> ppr x <> ppr " " <> ppr d
  ppr (x :=> y)     = ppr "(" <> ppr x <> ppr "->" <> ppr y <> ppr ")"
  ppr (Lit l)       = ppr l
  ppr (Forall as t) = ppr "forall" <> ppr as <> ppr t

-- The underlying shape
shape :: Type e -> Type S
{-# INLINE shape #-}
shape (Var a)       = Var a
shape (App a b)     = a -- EXPERIMENTAL
shape (Base b)      = Base b
shape (Data d)      = Base d
shape (Inj _ d)     = Base d
shape (a :=> b)     = shape a :=> shape b
shape (Lit l)       = Lit l
shape (Forall as t) = Forall as (shape t)

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
inj x (Forall as t) = Forall as (inj x t)

-- Replace refinement variables
-- TODO: Specialise
class Rename t where
  rename :: Int -> Int -> t -> t

instance Rename (Type e) where
  rename x y (Var a) = Var a
  rename x y (App a b) = App (rename x y a) (rename x y b)
  rename x y (Base b) = Base b
  rename x y (Data d) = Data d
  rename x y (Inj x' d)
    | x == x'   = Inj y d
    | otherwise = Inj x' d
  rename x y (a :=> b) = rename x y a :=> rename x y b
  rename x y (Lit l) = Lit l
  rename x y (Forall as t) = Forall as (rename x y t)









-- Convert from a core type
-- TODO: Specialise
class FromCore (e :: Extended) where
  type MT (e :: Extended) :: (* -> *) -> * -> *
  dataType :: Monad m => Core.TyCon -> MT e m (Type e)

instance FromCore S where
  type MT S = IdentityT
  dataType t = return $ Data t

fromCore :: (FromCore e, Monad m, Monad (MT e m)) => Core.Type -> MT e m (Type e)
fromCore (Tcr.TyVarTy a) = return $ Var $ Core.getName a
fromCore (Tcr.AppTy t1 t2) = do
  s1 <- runIdentityT $ fromCore t1
  s2 <- runIdentityT $ fromCore t2
  return $ App s1 s2
fromCore (Tcr.TyConApp t args)
  | Core.isTypeSynonymTyCon t
  , Just (as, u) <- Core.synTyConDefn_maybe t
  = fromCore (Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u)
 
  | refinable t 
  = dataType t

  | otherwise
  = return (Base t)
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l) = return $ Lit l
fromCore (Tcr.ForAllTy b t) = do
  let a = Core.getName $ Core.binderVar b
  t' <- fromCore t
  return $ Forall a t'
fromCore t = Core.pprPanic "Unexpected Cast or Coercion type" (Core.ppr t)

-- Partially instantiate type scheme
applyTyVars :: (FromCore e, Monad m, Monad (MT e m)) => Type e -> Core.Type -> MT e m (Type e)
applyTyVars (Forall a u) t = subTyVar a u t
  where
    subTyVar :: (FromCore e, Monad m, Monad (MT e m)) => Core.Name -> Type e -> Core.Type -> MT e m (Type e)
    subTyVar a (Var a') t 
      | a == a'    = fromCore t
      | otherwise  = return (Var a')
    subTyVar a (App x y) t = do
      x' <- runIdentityT $ subTyVar a x t
      y' <- runIdentityT $ subTyVar a y t
      return $ App x' y' 
    subTyVar a (x :=> y) t = do
      x' <- subTyVar a x t
      y' <- subTyVar a y t
      return (x' :=> y')
    subTyVar a (Forall a' u) t
      | a == a' = return (Forall a' u)
      | otherwise = do
        u' <- subTyVar a u t
        return $ Forall a' u'
    subTyVar _ (Base b) _ = return $ Base b
    subTyVar _ (Data d) _ = return $ Data d
    subTyVar _ (Inj x d) _ = return $ Inj x d
    subTyVar _ (Lit l) _ = return $ Lit l 
applyTyVars t _ = Core.pprPanic "Type scheme doesn't have that many type variables!" (Core.ppr t)

