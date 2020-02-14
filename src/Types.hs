{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Types (
  Extended(..),
  Type,
  IType,
  TypeGen(..),

  Scheme,
  IScheme,
  SchemeGen(..),
  pattern Mono,
  pattern Forall,
  constrain,

  Refined(..),
  refinable,

  inj,
  result,
  cmpShape,

  Promote(..),

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
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core

data Extended where
  S :: Extended -- Unrefined
  T :: Extended -- Refined

-- Monomorphic types
type Type  (e :: Extended) = TypeGen e Tcr.TyLit Core.TyCon
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

deriving instance Eq (Type s)

-- Promote/demote an interface type with the aide of a core type
class Promote tc l where
  promote :: Core.Type -> TypeGen e tc l -> Type e
  demote  :: TypeGen e tc l -> IType e

instance Promote IfaceTyLit IfaceTyCon where
  promote _ (Var a) = Var a
  promote (Tcr.AppTy a b) (App a' b') = App (promote a a') (promote b b')
  promote (Tcr.FunTy a b) (a' :=> b') = promote a a' :=> promote b b'
  promote (Tcr.TyConApp b as) (Base b' as')
    | toIfaceTyCon b == b' = Base b (fmap (uncurry promote) $ zip as as')
  promote (Tcr.TyConApp b as) (Data b' as')
    | toIfaceTyCon b == b' = Data b (fmap (uncurry promote) $ zip as as')
  promote (Tcr.TyConApp b as) (Inj x b' as')
    | toIfaceTyCon b == b' = Inj x b (fmap (uncurry promote) $ zip as as')
  promote (Tcr.LitTy l) (Lit l')
    | toIfaceTyLit l == l' = Lit l
  promote t1 t2 = Core.pprPanic "Promotion aide is incompatible!" (Core.ppr (t1, t2))

  demote = id

instance Promote Tcr.TyLit Core.TyCon where
  promote _ t = t

  demote (Var a)      = Var a
  demote (App a b)    = App (demote a) (demote b)
  demote (Base b as)  = Base (toIfaceTyCon b) (demote <$> as)
  demote (Data d as)  = Data (toIfaceTyCon d) (demote <$> as)
  demote (Inj x d as) = Inj x (toIfaceTyCon d) (demote <$> as)
  demote (a :=> b)    = demote a :=> demote b
  demote (Lit l)      = Lit (toIfaceTyLit l)
  demote Ambiguous    = Ambiguous

-- Polymorphic types
type Scheme (e :: Extended)  = SchemeGen (Type e)
type IScheme (e :: Extended) = SchemeGen (IType e)
data SchemeGen t c = Scheme {
  tyvars      :: [Core.Name],
  body        :: t,
  constraints :: c
}

pattern Mono :: t -> SchemeGen t ()
pattern Mono t = Scheme { tyvars = [], body = t, constraints = () }

pattern Forall :: [Core.Name] -> t -> SchemeGen t ()
pattern Forall as t = Scheme { tyvars = as, body = t, constraints = () }

constrain :: c -> SchemeGen t () -> SchemeGen t c
constrain c scheme = Scheme { tyvars  = tyvars scheme, body = body scheme, constraints = c }

-- Objects which are parameterised by refinement variables
class Refined t where
  domain :: t -> [Int]
  rename :: Int -> Int -> t -> t

instance Refined () where
  domain _   = []
  rename _ _ = id

instance Refined (TypeGen T l tc) where
  domain (Inj x _ as) = foldr (L.union . domain) [x] as
  domain (a :=> b)    = L.union (domain a) (domain b)
  domain _            = []

  rename x y (Inj x' d as)
    | x == x'              = Inj y d (rename x y <$> as)
    | otherwise            = Inj x' d (rename x y <$> as)
  rename x y (a :=> b)     = rename x y a :=> rename x y b
  rename _ _ t             = t

instance Refined c => Refined (SchemeGen (TypeGen T l e) c) where
  domain Scheme{ body = t, constraints = c } = domain t `L.union` domain c

  rename x y scheme@Scheme{ body = t, constraints = c } = scheme { body = rename x y t, constraints = rename x y c }

-- Clone of a Outputable (Core.Type)
instance (Outputable l, Outputable tc) => Outputable (TypeGen e l tc) where
  ppr = pprTy topPrec
    where
      pprTy :: (Outputable l, Outputable tc) => PprPrec -> TypeGen e l tc -> SDoc
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
      pprTy _ Ambiguous       = text "Ambiguous"

instance (Refined c, Outputable c, Outputable t) => Outputable (SchemeGen t c) where
  ppr Scheme{ tyvars = as , body = t, constraints = c } =
    hang (pprTyVars <> pprConVars <> ppr t)
       2 (hang (text "where") 2 (ppr c))
    where
      pprTyVars
        | null as   = text ""
        | otherwise = text "forall" <+> fsep (map ppr as) <> dot
      pprConVars
        | null (domain c) = text ""
        | otherwise       = text "forall" <+> fsep (map ppr (domain c)) <> dot

-- The shape of a type
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
cmpShape :: Type e -> Type e -> Bool
cmpShape t1 t2 = cmp (shape t1) (shape t2)
  where
    cmp Ambiguous _               = True
    cmp _ Ambiguous               = True
    cmp (Var _) (Var _)           = True  -- Type schemes may be unaligned??
    cmp (App a b) (App a' b')     = cmp a a' && cmp b b'
    cmp (Base b as) (Base b' as') = b == b' && all (uncurry cmp) (zip as as')
    cmp (a :=> b) (a' :=> b')     = cmp a a' && cmp b b'
    cmp (Lit l) (Lit l')          = l == l'
    cmp _ _                       = False

-- Inject a sort into a refinement environment
inj :: Int -> Type e -> Type T
inj _ (Var a)       = Var a
inj _ (App a b)     = App a b
inj _ (Base b as)   = Base b as
inj x (Data d as)   = Inj x d (inj x <$> as)
inj x (Inj _ d as)  = Inj x d (inj x <$> as)
inj x (a :=> b)     = inj x a :=> inj x b
inj _ (Lit l)       = Lit l
inj _ Ambiguous     = Ambiguous








-- Type application
applyType :: Scheme e () -> Type e -> Scheme e ()
applyType (Forall (a:as) u)   t = Forall as $ subTyVar a t u
applyType (Mono Ambiguous)    _ = Mono Ambiguous
applyType (Mono (Base b as))  t = Mono (Base b (as ++ [shape t]))
applyType (Mono (Data d as))  t = Mono (Data d (as ++ [t]))
applyType (Mono (Inj x d as)) t = Mono (Inj x d (as ++ [t]))
applyType (Mono (Var a))      t = Mono (App (Var a) (shape t))
applyType (Mono (App a b))    t = Mono (App (App a b) (shape t))
applyType t t' = Core.pprPanic "The type is saturated!" (Core.ppr (t, t'))

-- Type variable substitution
subTyVar :: Core.Name -> Type e -> Type e -> Type e
subTyVar a t (Var a')
  | a == a'    = t
  | otherwise  = Var a'
subTyVar a t (App x y) =
  case body $ applyType (Mono $ subTyVar a (shape t) x) $ subTyVar a (shape t) y of
    Base b as -> Base b as
    Var a     -> Var a
    App a b   -> App a b
    _         -> Core.pprPanic "Invalid aplication in types!" (Core.ppr (x, y))
subTyVar a t (x :=> y)    = subTyVar a t x :=> subTyVar a t y
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
    neg (Tcr.TyConApp _ _) = False -- Could this test wether tc' is refinable?
    neg (Tcr.TyVarTy _)     = False
    neg (Tcr.FunTy t1 t2)   = pos t1 && neg t2
    neg _                   = True

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
fromCore (Tcr.TyConApp tc args)
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
fromCoreScheme :: (MonadReader Core.Module m, FromCore m e) => Core.Type -> m (Scheme e ())
fromCoreScheme (Tcr.TyVarTy a)   = do
  n <- getExternalName a
  return $ Mono (Var n)
fromCoreScheme (Tcr.AppTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ Mono (App s1 s2)
fromCoreScheme (Tcr.TyConApp tc args)
  | Core.isTypeSynonymTyCon tc  -- Type synonym
  , Just (as, u) <- Core.synTyConDefn_maybe tc
    = fromCoreScheme (Core.substTy (Core.extendTvSubstList Core.emptySubst (zip as args)) u)
  | refinable tc
    = do
        args' <- mapM fromCore args
        -- uniqs <- take (Core.tyConArity tc - length args') <$> getUniquesM -- Quantify over unsaturated type variables
        -- let as = fmap (\u -> Core.mkInternalName u (Core.mkTyVarOcc "tc_arg") Core.noSrcSpan) uniqs
        -- Forall as <$> tycon tc (args' ++ (Var <$> as))
        t <- tycon tc args'
        return $ Mono t
  | otherwise
    = do
        args' <- mapM fromCore args
        -- uniqs <- take (Core.tyConArity tc - length args') <$> getUniquesM -- Quantify over unsaturated type variables
        -- let as = fmap (\u -> Core.mkInternalName u (Core.mkTyVarOcc "tc_arg") Core.noSrcSpan) uniqs
        -- return $ Forall as $ Base tc (args' ++ (Var <$> as))
        return $ Mono (Base tc args')
fromCoreScheme (Tcr.ForAllTy b t) = do
  let a = Core.getName $ Core.binderVar b
  scheme <- fromCoreScheme t
  return scheme{ tyvars = a : tyvars scheme }
fromCoreScheme (Tcr.FunTy t1 t2) = do
  s1     <- fromCore t1
  scheme <- fromCoreScheme t2
  return scheme{ body = s1 :=> body scheme }
fromCoreScheme (Tcr.LitTy l) = return $ Mono (Lit l)
fromCoreScheme t             = Core.pprPanic "Unexpected cast or coercion type!" (Core.ppr t)
