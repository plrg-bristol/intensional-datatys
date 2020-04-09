{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module FromCore (
  fromCore,
  fromCoreScheme,
  getExternalName,
  -- refinable,
) where

import Prelude hiding (sum)
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
class SrcDataType (e :: Extended) where
  datatype :: Monad m => DataType TyCon -> [Type S TyCon] -> InferM m (Type e TyCon)

instance SrcDataType S where
  datatype (_, d) as = return $ Base d as

instance SrcDataType T where
  datatype d as = do
    x <- fresh
    return $ Inj x d as

-- Convert a monomorphic core type
fromCore :: (SrcDataType e, Monad m) => [TyCon] -> Tcr.Type -> InferM m (Type e TyCon)
fromCore u (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore u (Tcr.AppTy t1 t2)   = do
  s1 <- fromCore u t1
  s2 <- fromCore u t2
  return $ App s1 s2
fromCore u (Tcr.TyConApp tc args)
  | isTypeSynonymTyCon tc  -- Type synonym
  , Just (as, s) <- synTyConDefn_maybe tc
    = fromCore u (substTy (extendTvSubstList emptySubst (zip as args)) s)
  | isClassTyCon tc = return Ambiguous
  | length (tyConDataCons tc) > 1
    = do
        args' <- mapM (fromCore (tc:u)) args
        datatype (tc `elem` u, tc) args'
  | otherwise
    = do
      args' <- mapM (fromCore (tc:u)) args
      return (Base tc args')
fromCore u (Tcr.FunTy t1 t2) = do
  s1 <- fromCore u t1
  s2 <- fromCore u t2
  return (s1 :=> s2)
fromCore u (Tcr.LitTy l)      = return $ Lit $ toIfaceTyLit l
fromCore u (Tcr.ForAllTy a t) = pprPanic "Unexpected polymorphic type!" $ ppr $ Tcr.ForAllTy a t
fromCore u t                  = pprPanic "Unexpected cast or coercion type!" $ ppr t

-- Convert a polymorphic core type
fromCoreScheme :: Monad m => [TyCon] -> Tcr.Type -> InferM m (Scheme TyCon)
fromCoreScheme u (Tcr.ForAllTy b t) = do
  a <- getExternalName (Tcr.binderVar b)
  scheme <- fromCoreScheme u t
  return scheme{ tyvars = a : tyvars scheme }
fromCoreScheme u (Tcr.FunTy t1 t2) = do
  s1     <- fromCore u t1
  scheme <- fromCoreScheme u t2 -- Is this safe??
  return scheme{ body = s1 :=> body scheme }
fromCoreScheme u (Tcr.CastTy t k)   = pprPanic "Unexpected cast type!" $ ppr (t, k)
fromCoreScheme u (Tcr.CoercionTy g) = pprPanic "Unexpected coercion type!" $ ppr g
fromCoreScheme u t                  = Mono <$> fromCore u t

-- Check whether a core datatype is refinable
-- refinable :: TyCon -> Bool
-- refinable tc = (length (tyConDataCons tc) > 1) && all pos (concatMap dataConOrigArgTys $ tyConDataCons tc)
--   where
--     pos :: Tcr.Type -> Bool
--     pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
--     pos _                 = True
-- 
--     neg :: Tcr.Type -> Bool
--     neg (Tcr.TyConApp _ _) = False -- Could this test whether tc' is refinable?
--     neg (Tcr.TyVarTy _)    = False
--     neg (Tcr.FunTy t1 t2)  = pos t1 && neg t2
--     neg _                  = True

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: (Monad m, NamedThing a) => a -> InferM m Name
getExternalName a = do
  let n = getName a
  mod <- getMod
  return $ mkExternalName (nameUnique n) mod (nameOccName n) (nameSrcSpan n)
