{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}

module InferM.FromCore
  ( fromCore,
    fromCoreScheme,
    fromCoreCons,
    fromCoreConsInst,
    getExternalName,
  )
where

-- refinable,

import CoreSubst
import DataCon
import InferM.Internal
import Name
import Outputable
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import TyCon
import Types
import Prelude hiding (sum)

-- Convert a core datatype
class SrcDataType (e :: Extended) where
  datatype :: Monad m => TyCon -> [Type S TyCon] -> InferM m (Type e TyCon)

instance SrcDataType S where
  datatype d = return . Data (Level0 d)

instance SrcDataType T where
  datatype d as = do
    x <- fresh
    return $ Inj x (Level0 d) as

-- Convert a monomorphic core type
fromCore :: (SrcDataType e, Monad m) => Tcr.Type -> InferM m (Type e TyCon)
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
    contra <- allowContra
    args' <- mapM fromCore args
    if refinable tc || contra
      then datatype tc args'
      else return (Base tc args')
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l) = return $ Lit $ toIfaceTyLit l
fromCore (Tcr.ForAllTy a t) = pprPanic "Unexpected polymorphic type!" $ ppr $ Tcr.ForAllTy a t
fromCore t = pprPanic "Unexpected cast or coercion type!" $ ppr t

-- Convert a polymorphic core type
fromCoreScheme :: Monad m => Tcr.Type -> InferM m (Scheme TyCon)
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
fromCoreCons :: Monad m => DataType DataCon -> InferM m (Scheme TyCon)
fromCoreCons k = do
  univ <- mapM getExternalName $ dataConUnivAndExTyCoVars (underlying k)
  args <- mapM (fmap under . fromCore) $ dataConOrigArgTys (underlying k)
  x <- fresh
  return $ Forall univ (foldr (:=>) (Inj x (d <$ k) (Var <$> univ)) (inj x <$> args))
  where
    d = dataConTyCon (underlying k)
    under :: Type S TyCon -> Type S TyCon
    under (Data d' as)
      | d == underlying d' = Data (Level1 d) as
    under (t :=> t') = under t :=> under t'
    under t = t

-- Extract a constructor's type with tyvars instantiated
-- We assume there are no existentially quantified tyvars
fromCoreConsInst :: Monad m => DataType DataCon -> [Type S TyCon] -> InferM m (Type T TyCon)
fromCoreConsInst k tyargs = do
  args <- mapM (fmap ((\t -> foldr (uncurry subTyVar) t (zip (fmap getName $ dataConUnivAndExTyCoVars $ underlying k) tyargs)) . under) . fromCore) $ dataConOrigArgTys (underlying k)
  x <- fresh
  return $ foldr (:=>) (Inj x (d <$ k) tyargs) (reverse $ inj x <$> args)
  where
    d = dataConTyCon (underlying k)
    under :: Type S TyCon -> Type S TyCon
    under (Data d' as)
      | d == underlying d' = Data (Level1 d) as
    under (t :=> t') = under t :=> under t'
    under t = t

-- Check whether a core datatype is refinable
refinable :: TyCon -> Bool
refinable tc = all pos (concatMap dataConOrigArgTys $ tyConDataCons tc)
  where
    pos :: Tcr.Type -> Bool
    pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
    pos _ = True
    neg :: Tcr.Type -> Bool
    neg (Tcr.TyConApp _ _) = False -- Could this test whether tc' is refinable?
    neg (Tcr.TyVarTy _) = False
    neg (Tcr.FunTy t1 t2) = pos t1 && neg t2
    neg _ = True

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: (Monad m, NamedThing a) => a -> InferM m Name
getExternalName a = do
  let n = getName a
  mod <- getMod
  return $ mkExternalName (nameUnique n) mod (nameOccName n) (nameSrcSpan n)
