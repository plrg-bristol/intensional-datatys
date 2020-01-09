{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Types (
  Extended(..),
  Type(..),
  mono,
  shape,
  inj,
  dataCon,
  refiableTyFunc,
  slice,
  subTyVar,
  subTyVarM,
  Refined(..),
  FromCore(..),
  fromCore,
) where

import Control.Monad 

import BasicTypes
import Outputable
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core

data Extended where
  S :: Extended -- Unrefined
  T :: Extended -- Refined

data Type (e :: Extended) where
  Var    :: Core.Name -> Type e
  App    :: Type e -> Type e -> Type e
  Base   :: Core.TyCon -> Type e
  Data   :: Core.TyCon -> Type S
  Inj    :: Int -> Core.TyCon -> Type T
  (:=>)  :: Type e -> Type e -> Type e
  Lit    :: Tcr.TyLit -> Type e
  Forall :: Core.Name -> Type e -> Type e

deriving instance Eq (Type e)

-- Objects which are parameterised by refinement variables
class Refined t where
  domain :: t -> [Int]
  rename :: Int -> Int -> t -> t

instance Refined (Type e) where
  domain (App a b)    = domain a ++ domain b
  domain (Inj x d)    = [x]
  domain (a :=> b)    = domain a ++ domain b
  domain (Forall _ t) = domain t
  domain _            = []

  rename x y (App a b)     = App (rename x y a) (rename x y b)
  rename x y (Inj x' d)
    | x == x'              = Inj y d
    | otherwise            = Inj x' d
  rename x y (a :=> b)     = rename x y a :=> rename x y b
  rename x y (Forall as t) = Forall as (rename x y t)
  rename _ _ t             = t

-- Clone of a Outputable (Core.Type)
instance Outputable (Type e) where
  ppr = pprTy topPrec
    where
      pprTy :: PprPrec -> Type e -> SDoc
      pprTy _ (Var a)        = ppr a
      pprTy prec (App t1 t2) = hang (pprTy prec t1)
                                  2 (pprTy appPrec t2)
      pprTy _ (Base b)       = ppr b
      pprTy _ (Data d)       = ppr d
      pprTy prec (Inj x d)   = maybeParen prec appPrec $ sep [text "inj", ppr x, ppr d]
      pprTy prec (t1 :=> t2) = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l)        = ppr l
      pprTy prec ty@Forall{}
        | (tvs, body) <- split ty
        = maybeParen prec funPrec $
          hang (text "forall" <+> fsep (map ppr tvs) Core.<> dot)
            2 (ppr body)
        where
          split ty | Forall tv ty' <- ty
                    , (tvs, body) <- split ty'
                    = (tv:tvs, body)
                    | otherwise
                    = ([], ty)

-- Force a type to be monomorphic
mono :: Type e -> Type e
mono (Var a)       = Var a
mono (App a b)     = App (mono a) (mono b)
mono (Base b)      = Base b
mono (Data d)      = Data d
mono (Inj x d)     = Inj x d
mono (a :=> b)     = mono a :=> mono b
mono (Lit l)       = Lit l
mono (Forall as t) = Core.pprPanic "Unexpected polymorphic type!" (Core.ppr (as, t))

-- The underlying shape
shape :: Type e -> Type S
shape (Var a)       = Var a
shape (App a b)     = App (shape a) (shape b)
shape (Base b)      = Base b
shape (Data d)      = Base d
shape (Inj _ d)     = Base d
shape (a :=> b)     = shape a :=> shape b
shape (Lit l)       = Lit l
shape (Forall as t) = Forall as (shape t)

-- Inject a sort into a refinement environment
inj :: Int -> Type e -> Type T
inj x (Var a)       = Var a
inj x (App a b)     = App (inj x a) (inj x b)
inj x (Base b)      = Base b
inj x (Data d)      = Inj x d
inj x (Inj _ d)     = Inj x d
inj x (a :=> b)     = inj x a :=> inj x b
inj x (Lit l)       = Lit l
inj x (Forall as t) = Forall as (inj x t)

dataCon :: Type T -> ([Type T], Type T)
dataCon (a :=> b) = (a:args, res)
  where
    (args, res) = dataCon b
dataCon (App a b)     = dataCon a
dataCon (Forall as t) = dataCon t
dataCon t = ([], t)

-- Does the head of an application correspond to a refinable datatype
refiableTyFunc :: Type T -> Bool
refiableTyFunc Inj{}     = True
refiableTyFunc (App h _) = refiableTyFunc h
refiableTyFunc _         = False

-- TODO: Check this is sound!!
refinable :: Core.TyCon -> Bool
refinable tc = (length (Core.tyConDataCons tc) > 1) && all pos (concatMap Core.dataConOrigArgTys $ Core.tyConDataCons tc)
  where
    pos :: Core.Type -> Bool
    pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
    pos _                 = True

    neg :: Core.Type -> Bool
    neg (Tcr.TyConApp tc' _)               = False -- Test wether tc' is refinable?
    neg (Tcr.TyVarTy _)   = False
    neg (Tcr.FunTy t1 t2) = pos t1 && neg t2
    neg _                 = True

-- Take the slice of a datatype
slice :: [Core.TyCon] -> [Core.TyCon]
slice tcs
  | tcs' == tcs = tcs
  | otherwise   = slice tcs'
  where
    tcs' = [tc' | tc <- tcs
                , dc <- Core.tyConDataCons tc
                , (Tcr.TyConApp tc' _) <- Core.dataConOrigArgTys dc
                , tc' `notElem` tcs
                , refinable tc'] 
                ++ tcs

-- Convert from a core type
class Monad m => FromCore m (e :: Extended) where
  dataType :: Core.TyCon -> m (Type e)

instance Monad m => FromCore m S where
  dataType t = return $ Data t

fromCore :: FromCore m e => Core.Type -> m (Type e)
fromCore (Tcr.TyVarTy a)   = return $ Var $ Core.getName a
fromCore (Tcr.AppTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ App s1 s2
fromCore (Tcr.TyConApp t args)
  | Core.isTypeSynonymTyCon t
  , Just (as, u) <- Core.synTyConDefn_maybe t
  = fromCore (Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u)
  | refinable t
  = do
      args' <- mapM fromCore args
      t' <- dataType t
      return $ foldl App t' args' -- These need Forall is args isn't long enough
  
  | otherwise
  = do
      args' <- mapM fromCore args
      return $ foldl App (Base t) args'

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

-- Substitute type variable
subTyVar :: Core.Name -> Type e -> Type e -> Type e
subTyVar a t (Var a') 
  | a == a'    = t
  | otherwise  = Var a'
subTyVar a t (App x y) = App (subTyVar a t x) (subTyVar a t y)
subTyVar a t (x :=> y) = subTyVar a t x :=> subTyVar a t y
subTyVar a t (Forall a' u)
  | a == a'    = Forall a' u
  | otherwise  = Forall a' (subTyVar a t u)
subTyVar _ _ t = t

-- Substitute type variable directly from core type
subTyVarM :: FromCore m e => Core.Name -> Core.Type -> Type e -> m (Type e)
subTyVarM a t (Var a') 
  | a == a'    = fromCore t
  | otherwise  = return (Var a')
subTyVarM a t (App x y) = do
  x' <- subTyVarM a t x
  y' <- subTyVarM a t y
  return (App x' y')
subTyVarM a t (x :=> y) = do
  x' <- subTyVarM a t x
  y' <- subTyVarM a t y
  return (x' :=> y')
subTyVarM a t (Forall a' u)
  | a == a'   = return $ Forall a' u
  | otherwise = do
    u' <- subTyVarM a t u
    return $ Forall a' u'
subTyVarM _ _ t = return t