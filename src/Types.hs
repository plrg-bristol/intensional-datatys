{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module Types (
  Extended(..),
  Type,
  IType,
  TypeGen(..),
  Scheme(..),
  Refined(..),

  shape,
  result,
  compareShape,
  inj,
  refinable,
  promote,
  demote,

  applyType,
  subTyVar,

  FromCore(..),
  getExternalName,
  fromCore,
  fromCoreScheme,
) where

import Prelude hiding ((<>))

import Control.Monad.Reader

import qualified Data.List as L

import BasicTypes
import Outputable
import IfaceType
import ToIface
-- import UniqSupply
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core

data Extended where
  S :: Extended -- Unrefined
  T :: Extended -- Refined

-- Monomorphic types
type Type (e :: Extended) = TypeGen e Tcr.TyLit Core.TyCon
type IType (e :: Extended) = TypeGen e IfaceTyLit IfaceTyCon
data TypeGen (e :: Extended) l tc where
  Var    :: Core.Name -> TypeGen e l tc
  App    :: TypeGen S l tc -> TypeGen S l tc -> TypeGen e l tc
  Base   :: tc -> [TypeGen S l tc] -> TypeGen e l tc
  Data   :: tc -> [TypeGen S l tc] -> TypeGen S l tc
  Inj    :: Int -> tc -> [TypeGen T l tc] -> TypeGen T l tc
  (:=>)  :: TypeGen e l tc -> TypeGen e l tc -> TypeGen e l tc
  Lit    :: l -> TypeGen e l tc

  Ambiguous :: TypeGen e l tc -- Ambiguous type hides higher ranked types and casts from inference

deriving instance Eq (Type e)

-- Polymorphic types
data Scheme (e :: Extended) where
  Forall :: [Core.Name] -> Type e -> Scheme e

deriving instance Eq (Scheme e)

-- Objects which are parameterised by refinement variables
class Refined t where
  domain :: t -> [Int]
  rename :: Int -> Int -> t -> t

instance Refined (TypeGen T l tc) where
  domain (Inj x d as) = foldr (L.union . domain) [x] as
  domain (a :=> b)    = L.union (domain a) (domain b)
  domain _            = []

  rename x y (App a b)     = App a b
  rename x y (Inj x' d as)
    | x == x'              = Inj y d (rename x y <$> as)
    | otherwise            = Inj x' d (rename x y <$> as)
  rename x y (a :=> b)     = rename x y a :=> rename x y b
  rename _ _ t             = t

instance Refined (Scheme T) where
  domain (Forall as t) = domain t

  rename x y (Forall as t) = Forall as $ rename x y t

-- Clone of a Outputable (Core.Type)
instance (Outputable l, Outputable tc) => Outputable (TypeGen e l tc) where
  ppr = pprTy topPrec
    where
      pprTy :: (Outputable l, Outputable tc) => PprPrec -> TypeGen e l tc -> SDoc
      pprTy _ (Var a)         = ppr a
      pprTy prec (App t1 t2)  = hang (pprTy prec t1)
                                   2 (pprTy appPrec t2)
      pprTy prec (Base b as)  = hang (ppr b)
                                   2 (sep $ fmap (\a -> text "@" <> pprTy appPrec a) as)
      pprTy prec (Data d as)  = hang (ppr d)
                                   2 (sep $ fmap (\a -> text "@" <> pprTy appPrec a) as)
      pprTy prec (Inj x d as) = hang (maybeParen prec appPrec $ sep [text "inj", ppr x, ppr d])
                                   2 (sep $ fmap (\a -> text "@" <> pprTy appPrec a) as)
      pprTy prec (t1 :=> t2)  = maybeParen prec funPrec $ sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l)         = ppr l
      pprTy _ Ambiguous       = text "Ambiguous"

instance Outputable (Scheme e) where
  ppr (Forall as t)
    | null as   = ppr t
    | otherwise = maybeParen topPrec funPrec $
                        hang (text "forall" <+> fsep (map ppr as) Core.<> dot)
                           2 (ppr t)

-- The underlying shape
shape :: Type e -> Type S
shape (Var a)       = Var a
shape (App a b)     = App (shape a) (shape b)
shape (Base b as)   = Base b (shape <$> as)
shape (Data d as)   = Base d (shape <$> as)
shape (Inj _ d as)  = Base d (shape <$> as)
shape (a :=> b)     = shape a :=> shape b
shape (Lit l)       = Lit l
shape Ambiguous     = Ambiguous

-- Extract the result type from a curried function
result :: Type T -> ([Type T], Type T)
result (a :=> b) = (a:args, res)
  where
    (args, res) = result b
result t = ([], t)

-- Comapre shapes
compareShape :: Type S -> Type S -> Bool
compareShape Ambiguous _               = True
compareShape _ Ambiguous               = True
compareShape (Var _) (Var _)           = True -- Type schemes may be unaligned
compareShape (App a b) (App a' b')     = compareShape a a' && compareShape b b'
compareShape (Base b as) (Base b' as') = b == b' && all (uncurry compareShape) (zip as as')
compareShape (a :=> b) (a' :=> b')     = compareShape a a' && compareShape b b'
compareShape (Lit l) (Lit l')          = l == l'
compareShape _ _                       = False

-- Inject a sort into a refinement environment
inj :: Int -> Type e -> Type T
inj x (Var a)       = Var a
inj x (App a b)     = App a b
inj x (Base b as)   = Base b as
inj x (Data d as)   = Inj x d (inj x <$> as)
inj x (Inj _ d as)  = Inj x d (inj x <$> as)
inj x (a :=> b)     = inj x a :=> inj x b
inj x (Lit l)       = Lit l

-- Promote an interface type with the aide of a core type
promote :: Core.Kind -> IType e -> Type e
promote t1 t2 | Core.pprTrace "lift" (Core.ppr (t1, t2)) True = undefined

demote :: Type e -> IType e
demote (Var a) = Var a
demote (App a b) = App (demote a) (demote b)
demote (Base b as) = Base (toIfaceTyCon b) (demote <$> as)
demote (Data d as) = Data (toIfaceTyCon d) (demote <$> as)
demote (Inj x d as) = Inj x (toIfaceTyCon d) (demote <$> as)
demote (a :=> b) = demote a :=> demote b
demote (Lit l) = Lit (toIfaceTyLit l)








-- Type application
applyType :: Scheme e -> Type e -> Scheme e
applyType (Forall [] Ambiguous) t    = Forall [] Ambiguous
applyType (Forall [] (Base b as)) t  = Forall [] (Base b (as ++ [shape t]))
applyType (Forall [] (Data d as)) t  = Forall [] (Data d (as ++ [t]))
applyType (Forall [] (Inj x d as)) t = Forall [] (Inj x d (as ++ [t]))
applyType (Forall [] (Var a)) t      = Forall [] (App (Var a) (shape t))
applyType (Forall [] (App a b)) t    = Forall [] (App (App a b) (shape t))
applyType (Forall (a:as) u) t        = Forall as (subTyVar a t u)
applyType t t'                       = Core.pprPanic "The type is saturated!" (Core.ppr (t, t'))

-- Type variable substitution
subTyVar :: Core.Name -> Type e -> Type e -> Type e
subTyVar a t (Var a')
  | a == a'    = t
  | otherwise  = Var a'
subTyVar a t (App x y) =
  case applyType (Forall [] $ subTyVar a (shape t) x) (subTyVar a (shape t) y) of
    Forall [] (Base b as) -> Base b as
    Forall [] (Var a)     -> Var a
    Forall [] (App a b)   -> App a b
subTyVar a t (x :=> y) = subTyVar a t x :=> subTyVar a t y
subTyVar a t (Base b as)  = Base b (subTyVar a (shape t) <$> as)
subTyVar a t (Data d as)  = Data d (subTyVar a t <$> as)
subTyVar a t (Inj x d as) = Inj x d (subTyVar a t <$> as)
subTyVar _ _ t = t




-- Check whether a core type is refinable
refinable :: Core.TyCon -> Bool
refinable tc = (length (Core.tyConDataCons tc) > 1) && all pos (concatMap Core.dataConOrigArgTys $ Core.tyConDataCons tc)
  where
    pos :: Core.Type -> Bool
    pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
    pos _                 = True

    neg :: Core.Type -> Bool
    neg (Tcr.TyConApp tc' _) = False -- Could this test wether tc' is refinable?
    neg (Tcr.TyVarTy _)      = False
    neg (Tcr.FunTy t1 t2)    = pos t1 && neg t2
    neg _                    = True

-- Convert from a core type
class Monad m => FromCore m (e :: Extended) where
  tycon :: Core.TyCon -> [Type e] -> m (Type e)

instance Monad m => FromCore m S where
  tycon d as = return $ Data d as

getExternalName :: MonadReader Core.Module m => Core.NamedThing a => a -> m Core.Name
getExternalName a = do
  let n = Core.getName a
  m <- ask
  return $ Core.mkExternalName (Core.nameUnique n) m (Core.nameOccName n) (Core.nameSrcSpan n)

fromCore :: (MonadReader Core.Module m, FromCore m e) => Core.Type -> m (Type e)
fromCore (Tcr.TyVarTy a)   = Var <$> getExternalName a
fromCore (Tcr.AppTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ App s1 s2
fromCore t@(Tcr.TyConApp tc args)
  | Core.isTypeSynonymTyCon tc  -- Type synonym
  , Just (as, u) <- Core.synTyConDefn_maybe tc
    = fromCore (Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u)
  -- | Core.tyConArity tc /= length args
  --  = Core.pprPanic "Type constructor must be fully isntantiated!" (Core.ppr t)
  | refinable tc
    = do
        args' <- mapM fromCore args
        tycon tc args'
  | otherwise
    = do
        args' <- mapM fromCore args
        return $ Base tc args'
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l) = return $ Lit l
fromCore t@Tcr.ForAllTy{} = Core.pprPanic "Unexpected polymorphic type!" (Core.ppr t)
fromCore t                = Core.pprPanic "Unexpected cast or coercion type!" (Core.ppr t)

-- Convert a polymorphic core type
fromCoreScheme :: (MonadReader Core.Module m, FromCore m e) => Core.Type -> m (Scheme e)
fromCoreScheme (Tcr.TyVarTy a)   = Forall [] . Var <$> getExternalName a
fromCoreScheme (Tcr.AppTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ Forall [] $ App s1 s2
fromCoreScheme t@(Tcr.TyConApp tc args)
  | Core.isTypeSynonymTyCon tc  -- Type synonym
  , Just (as, u) <- Core.synTyConDefn_maybe tc
    = fromCoreScheme (Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u)
  | refinable tc
    = do
        args' <- mapM fromCore args
        -- uniqs <- take (Core.tyConArity tc - length args') <$> getUniquesM -- Quantify over unsaturated type variables
        -- let as = fmap (\u -> Core.mkInternalName u (Core.mkTyVarOcc "tc_arg") Core.noSrcSpan) uniqs
        -- Forall as <$> tycon tc (args' ++ (Var <$> as))
        Forall [] <$> tycon tc args'
  | otherwise
    = do
        args' <- mapM fromCore args
        -- uniqs <- take (Core.tyConArity tc - length args') <$> getUniquesM -- Quantify over unsaturated type variables
        -- let as = fmap (\u -> Core.mkInternalName u (Core.mkTyVarOcc "tc_arg") Core.noSrcSpan) uniqs
        -- return $ Forall as $ Base tc (args' ++ (Var <$> as))
        return $ Forall [] $ Base tc args'
fromCoreScheme (Tcr.ForAllTy b t) = do
  let a = Core.getName $ Core.binderVar b
  Forall as t' <- fromCoreScheme t
  return $ Forall (a:as) t'
fromCoreScheme (Tcr.FunTy t1 t2) = do
  s1           <- fromCore t1
  Forall as s2 <- fromCoreScheme t2
  return $ Forall as (s1 :=> s2)
fromCoreScheme (Tcr.LitTy l) = return $ Forall [] $ Lit l
fromCoreScheme t             = Core.pprPanic "Unexpected cast or coercion type!" (Core.ppr t)
