{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}

module FromCore
  ( fromCore,
    fromCoreScheme,
    fromCoreCons,
    fromCoreConsInst,
    getExternalName,
    getVar,
  )
where

import ConGraph
import Constraints
import Control.Monad.RWS.Strict
import qualified Data.List as L
import qualified Data.Map as M
import DataTypes
import GhcPlugins hiding (Expr (..), Type)
import InferM
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import Types

-- Convert a core datatype to the internal representation
class CoreDataType (e :: Extended) where
  mkDataType :: TyCon -> [Type 'S] -> InferM s (Type e)

instance CoreDataType 'S where
  mkDataType d as = do
    u <- asks unrollDataTypes
    return $ Data (DataType (if u then Initial else Neutral) d) as

instance CoreDataType 'T where
  mkDataType d as = do
    x <- fresh
    u <- asks unrollDataTypes
    return $ Inj x (DataType (if u then Initial else Neutral) d) as

-- Convert a monomorphic core type
fromCore :: CoreDataType e => Tcr.Type -> InferM s (Type e)
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
    c <- asks allowContra
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
fromCoreScheme :: Tcr.Type -> InferM s (Scheme s)
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
fromCoreCons :: DataType DataCon -> InferM s (Scheme s)
fromCoreCons k = do
  let d = dataConTyCon (orig k)
  x <- fresh
  args <- mapM fromCore $ dataConOrigArgTys (orig k)
  -- Unroll datatype
  u <- asks unrollDataTypes
  let args' = if u then fmap (increaseLevel d) args else args :: [Type 'S]
  -- Inject
  let args'' = fmap (inj x) args'
  -- Rebuild type
  univ <- mapM getExternalName $ dataConUnivAndExTyCoVars (orig k)
  let res = Inj x (d <$ k) (Var <$> univ)
  return $ Forall univ (foldr (:=>) res args'')

-- Extract a constructor's type with tyvars instantiated
-- We assume there are no existentially quantified tyvars
fromCoreConsInst :: DataType DataCon -> [Type 'S] -> InferM s (Type 'T)
fromCoreConsInst k tyargs = do
  let d = dataConTyCon (orig k)
  x <- fresh
  args <- mapM fromCore $ dataConOrigArgTys (orig k)
  -- Unroll datatype
  u <- asks unrollDataTypes
  let args' = if u then fmap (increaseLevel d) args else args
  -- Instantiate and inject
  let args'' = fmap (inj x . inst) args'
  -- Rebuild type
  let res = Inj x (d <$ k) tyargs
  return $ foldr (:=>) res (reverse args'')
  where
    inst :: Type 'S -> Type 'S
    inst t = foldr (uncurry subTyVar) t (zip (fmap getName $ dataConUnivAndExTyCoVars $ orig k) tyargs)

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: NamedThing a => a -> InferM s Name
getExternalName a = do
  let n = getName a
  mn <- asks modName
  return $ mkExternalName (nameUnique n) mn (nameOccName n) (nameSrcSpan n)

-- Lookup constrained variable emit its constraints
getVar :: Var -> InferM s (Scheme s)
getVar v =
  asks (M.lookup (getName v) . varEnv) >>= \case
    Just scheme -> do
      -- Localise constraints
      xys <-
        mapM
          ( \x -> do
              y <- fresh
              return (x, y)
          )
          (L.sort $ boundvs scheme)
      fre_scheme <- renameAll xys scheme {boundvs = []}
      case constraints fre_scheme of
        Nothing ->
          -- ? In this case is the variable necessarily unsatisfiable
          return fre_scheme {constraints = Nothing}
        Just var_cg -> do
          g <- asks branchGuard
          var_cg' <- guardWith g var_cg
          modify (\s -> s {congraph = unionUniq (congraph s) var_cg'})
          return fre_scheme {constraints = Nothing}
    Nothing -> do
      -- Maximise library type
      var_scheme <- fromCoreScheme $ varType v
      maximise True (body var_scheme)
      return var_scheme

-- Maximise/minimise a type
maximise :: Bool -> Type 'T -> InferM s ()
maximise True (Inj x d _) = do
  l <- asks inferLoc
  mapM_ (\k -> emit (Con (getName k) l) (Dom x) d) $ tyConDataCons (orig d)
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()
