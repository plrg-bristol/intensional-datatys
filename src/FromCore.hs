{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module FromCore (
  fromCore,
  fromCoreScheme,
  getExternalName,
  refinable,
) where

import Name
import TyCon
import DataCon
import ToIface
import CoreSubst
import Outputable
import qualified TyCoRep as Tcr

import Types
import Scheme
import InferM.Internal

-- Convert a core datatype
class DataType (e :: Extended) where
  datatype :: Monad m => TyCon -> [Type e TyCon] -> InferM m (Type e TyCon)

instance DataType S where
  datatype d as = return $ Data d as

instance DataType T where
  datatype d as = do
    x <- fresh
    return $ Inj x d as

-- Convert a monomorphic core type
fromCore :: (DataType e, Monad m) => Tcr.Type -> InferM m (Type e TyCon)
fromCore (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore (Tcr.AppTy t1 t2)   = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ App s1 s2
fromCore (Tcr.TyConApp tc args)
  | isTypeSynonymTyCon tc  -- Type synonym
  , Just (as, u) <- synTyConDefn_maybe tc
    = fromCore (substTy (extendTvSubstList emptySubst (zip as args)) u)
  | refinable tc
    = do
        args' <- mapM fromCore args
        datatype tc args'
  | otherwise
    = do
        args' <- mapM fromCore args
        return $ Base tc args'
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l)      = return $ Lit $ toIfaceTyLit l
fromCore (Tcr.ForAllTy a t) = pprPanic "Unexpected polymorphic type!" $ ppr $ Tcr.ForAllTy a t
fromCore t                  = pprPanic "Unexpected cast or coercion type!" $ ppr t

-- Convert a polymorphic core type
fromCoreScheme :: Monad m => Tcr.Type -> InferM m (Scheme TyCon)
fromCoreScheme (Tcr.ForAllTy b t) = do
  a <- getExternalName (Tcr.binderVar b)
  scheme <- fromCoreScheme t
  return scheme{ tyvars = a : tyvars scheme }
fromCoreScheme (Tcr.FunTy t1 t2) = do
  s1     <- fromCore t1
  scheme <- fromCoreScheme t2 -- Is this safe??
  return scheme{ body = s1 :=> body scheme }
fromCoreScheme (Tcr.CastTy t k)   = pprPanic "Unexpected cast type!" $ ppr (t, k)
fromCoreScheme (Tcr.CoercionTy g) = pprPanic "Unexpected coercion type!" $ ppr g
fromCoreScheme t                  = Mono <$> fromCore t

-- Check whether a core datatype is refinable
refinable :: TyCon -> Bool
refinable tc = (length (tyConDataCons tc) > 1) && all pos (concatMap dataConOrigArgTys $ tyConDataCons tc)
  where
    pos :: Tcr.Type -> Bool
    pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
    pos _                 = True

    neg :: Tcr.Type -> Bool
    neg (Tcr.TyConApp _ _) = False -- Could this test whether tc' is refinable?
    neg (Tcr.TyVarTy _)    = False
    neg (Tcr.FunTy t1 t2)  = pos t1 && neg t2
    neg _                  = True

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: (Monad m, NamedThing a) => a -> InferM m Name
getExternalName a = do
  let n = getName a
  mod <- getMod
  return $ mkExternalName (nameUnique n) mod (nameOccName n) (nameSrcSpan n)
