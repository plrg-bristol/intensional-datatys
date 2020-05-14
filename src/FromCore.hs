{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module FromCore
  ( fromCore,
    fromCoreScheme,
    fromCoreCons,
    fromCoreConsInst,
    getExternalName,
  )
where

import Control.Lens
import Control.Monad.RWS
import DataTypes
import GhcPlugins hiding (Expr (..), Type)
import Guards
import IfaceType
import InferM
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import Types

-- Convert a core datatype to the internal representation
class CoreDataType (e :: Extended) where
  mkDataType :: Monad m => TyCon -> [Type S TyCon] -> InferM s m (Type e TyCon)

instance CoreDataType S where
  mkDataType d as = do
    u <- view unrollDataTypes
    if u
      then return $ Data (Level0 d) as
      else return $ Data (Neutral d) as

instance CoreDataType T where
  mkDataType d as = do
    x <- freshRVar <<+= 1
    u <- view unrollDataTypes
    if u
      then return $ Inj x (Level0 d) as
      else return $ Inj x (Neutral d) as

-- Convert a monomorphic core type
fromCore :: (CoreDataType e, Monad m) => Tcr.Type -> InferM s m (Type e TyCon)
fromCore (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore (Tcr.AppTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ App s1 s2
fromCore (Tcr.TyConApp tc args)
  | isTypeSynonymTyCon tc, -- Type synonym
    Just (as, s) <- synTyConDefn_maybe tc =
    fromCore (substTy (extendTvSubstList emptySubst (zip as args)) s)
  | isClassTyCon tc = return Ambiguous
  | otherwise = do
    args' <- mapM fromCore args
    c <- view allowContra
    if trivial tc || (contravariant tc && not c)
      then return (Base tc args')
      else mkDataType tc args'
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l) = return $ Lit $ toIfaceTyLit l
fromCore (Tcr.ForAllTy a t) = pprPanic "Unexpected polymorphic type!" $ ppr $ Tcr.ForAllTy a t
fromCore t = pprPanic "Unexpected cast or coercion type!" $ ppr t

-- Convert a polymorphic core type
fromCoreScheme :: Monad m => Tcr.Type -> InferM s m (Scheme TyCon (GuardSet s))
fromCoreScheme (Tcr.ForAllTy b t) = do
  a <- getExternalName (Tcr.binderVar b)
  scheme <- fromCoreScheme t
  return scheme {tyvars = a : tyvars scheme}
fromCoreScheme (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  scheme <- fromCoreScheme t2 -- Is this safe??
  return scheme {body = s1 :=> body scheme}
fromCoreScheme (Tcr.CastTy t k) = pprPanic "Unexpected cast type!" $ ppr (t, k)
fromCoreScheme (Tcr.CoercionTy g) = pprPanic "Unexpected coercion type!" $ ppr g
fromCoreScheme t = Mono <$> fromCore t

-- Extract a constructor's original type
fromCoreCons :: Monad m => DataType DataCon -> InferM s m (Scheme TyCon (GuardSet s))
fromCoreCons k = do
  let d = dataConTyCon (underlying k)

  x <- freshRVar <<+= 1
  args <- mapM fromCore $ dataConOrigArgTys (underlying k)

  -- Unroll datatype
  u <- view unrollDataTypes
  let args' = if u then fmap (unrollUnder d) args else args :: [Type S TyCon]

  -- Inject
  let args'' = fmap (inj x) args'

  -- Rebuild type
  univ <- mapM getExternalName $ dataConUnivAndExTyCoVars (underlying k)
  let res = Inj x (d <$ k) (Var <$> univ)
  return $ Forall univ (foldr (:=>) res args'')

-- Extract a constructor's type with tyvars instantiated
-- We assume there are no existentially quantified tyvars
fromCoreConsInst :: Monad m => DataType DataCon -> [Type S TyCon] -> InferM s m (Type T TyCon)
fromCoreConsInst k tyargs = do
  let d = dataConTyCon (underlying k)

  x <- freshRVar <<+= 1
  args <- mapM fromCore $ dataConOrigArgTys (underlying k)

  -- Unroll datatype
  u <- view unrollDataTypes
  let args' = if u then fmap (unrollUnder d) args else args

  -- Instantiate and inject
  let args'' = fmap (inj x . inst) args'

  -- Rebuild type
  let res = Inj x (d <$ k) tyargs
  return $ foldr (:=>) res (reverse args'')
  where
    inst :: Type S TyCon -> Type S TyCon
    inst t = foldr (uncurry subTyVar) t (zip (fmap getName $ dataConUnivAndExTyCoVars $ underlying k) tyargs)

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: (Monad m, NamedThing a) => a -> InferM s m Name
getExternalName a = do
  let n = getName a
  mod <- view modName
  return $ mkExternalName (nameUnique n) mod (nameOccName n) (nameSrcSpan n)
