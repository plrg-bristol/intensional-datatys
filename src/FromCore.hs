{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module FromCore (
  fromCore,
  fromCoreScheme
) where

import Types
import Scheme
import InferM

import Name
import TyCon
import Module
import ToIface
import DataCon
import IfaceType
import CoreSubst
import Outputable
import qualified TyCoRep as Tcr

-- Convert a core datatype
class DataType (e :: Extended) where
  datatype :: Monad m => IfaceTyCon -> [Type e] -> InferM m (Type e)

instance DataType S where
  datatype d as = return $ Data d as

instance DataType T where
  datatype d as = do
    x <- fresh
    return $ Inj x d as

-- Check whether a core datatype is refinable
refinable :: TyCon -> Bool
refinable tc = (length (tyConDataCons tc) > 1) && all pos (concatMap dataConOrigArgTys $ tyConDataCons tc)
  where
    pos :: Tcr.Type -> Bool
    pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
    pos _                 = True

    neg :: Tcr.Type -> Bool
    neg (Tcr.TyConApp _ _) = False -- Could this test wether tc' is refinable?
    neg (Tcr.TyVarTy _)     = False
    neg (Tcr.FunTy t1 t2)   = pos t1 && neg t2
    neg _                   = True

-- Prepare name for interface
getExternalName :: (Monad m, NamedThing a) => a -> InferM m Name
getExternalName a = do
  let n = getName a
  mod <- getMod
  return $ mkExternalName (nameUnique n) mod (nameOccName n) (nameSrcSpan n)

-- Convert a monomorphic core type
fromCore :: (DataType e, Monad m) => Tcr.Type -> InferM m (Type e)
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
        datatype (toIfaceTyCon tc) args'
  | otherwise
    = do
        args' <- mapM fromCore args
        return $ Base (toIfaceTyCon tc) args'
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l)      = return $ Lit $ toIfaceTyLit l
fromCore (Tcr.ForAllTy a t) = pprPanic "Unexpected polymorphic type!" $ ppr $ Tcr.ForAllTy a t
fromCore t                  = pprPanic "Unexpected cast or coercion type!" $ ppr t

-- Convert a polymorphic core type
fromCoreScheme :: (DataType e, Monad m) => Tcr.Type -> InferM m (Scheme e ())
fromCoreScheme (Tcr.ForAllTy b t) = do
  let a = getName $ Tcr.binderVar b
  scheme <- fromCoreScheme t
  return scheme{ tyvars = a : tyvars scheme }
fromCoreScheme (Tcr.FunTy t1 t2) = do
  s1     <- fromCore t1
  scheme <- fromCoreScheme t2 -- Is this safe??
  return scheme{ body = s1 :=> body scheme }
fromCoreScheme (Tcr.CastTy t k) = pprPanic "Unexpected cast type!" $ ppr (t, k)
fromCoreScheme (Tcr.CoercionTy g) = pprPanic "Unexpected coercion type!" $ ppr g
fromCoreScheme t            = Mono <$> fromCore t
