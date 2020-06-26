{-# LANGUAGE LambdaCase #-}

module FromCore
  ( fromCore,
    fromCoreScheme,
    getVar,
  )
where

import Constraints
import Constructors
import Control.Monad.RWS
import qualified Data.Map as M
import DataTypes
import GhcPlugins hiding (Expr (..), Type, (<>))
import InferM
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import Types

-- Convert a monomorphic core type with fresh refinement variables
fromCore :: Tcr.Type -> InferM Type
fromCore (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore (Tcr.AppTy a b) = liftM2 App (fromCore a) (fromCore b)
fromCore (Tcr.TyConApp d as)
  | isTypeSynonymTyCon d,
    Just (as', s) <- synTyConDefn_maybe d =
    fromCore (substTy (extendTvSubstList emptySubst (zip as' as)) s) -- Instantiate type synonyms
  | isClassTyCon d = return Ambiguous -- Disregard type class evidence
  | trivial d = Data (Base d) <$> mapM fromCore as -- Datatypes with only one constructor
  | otherwise = do
    x <- fresh
    Data (Inj x d) <$> mapM fromCore as
fromCore (Tcr.FunTy a b) = liftM2 (:=>) (fromCore a) (fromCore b)
fromCore (Tcr.LitTy l) = return $ Lit $ toIfaceTyLit l
fromCore (Tcr.ForAllTy a t) = pprPanic "Unexpected polymorphic type!" $ ppr $ Tcr.ForAllTy a t
fromCore (Tcr.CastTy t k) = pprPanic "Unexpected cast type!" $ ppr (t, k)
fromCore (Tcr.CoercionTy g) = pprPanic "Unexpected coercion type!" $ ppr g

-- Convert a polymorphic core type
fromCoreScheme :: Tcr.Type -> InferM Scheme
fromCoreScheme (Tcr.ForAllTy b t) = do
  a <- getExternalName (Tcr.binderVar b)
  scheme <- fromCoreScheme t
  return scheme {tyvars = a : tyvars scheme}
fromCoreScheme (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  scheme <- fromCoreScheme t2 -- Optimistically push arrows inside univiersal quantifier
  return scheme {body = s1 :=> body scheme}
fromCoreScheme (Tcr.CastTy t k) = pprPanic "Unexpected cast type!" $ ppr (t, k)
fromCoreScheme (Tcr.CoercionTy g) = pprPanic "Unexpected coercion type!" $ ppr g
fromCoreScheme t = Mono <$> fromCore t

-- -- Extract a constructor's original type
-- fromCoreCons :: DataCon -> InferM Scheme
-- fromCoreCons k = do
--   let d = dataConTyCon k
--   x <- fresh
--   args <- mapM fromCore $ dataConOrigArgTys k
--   -- Unroll datatype
--   -- u <- asks unrollDataTypes
--   -- let args' = if u then fmap (increaseLevel d) args else args :: [Type 'S]
--   -- Inject
--   let args' = fmap (inj x) args
--   -- Rebuild type
--   univ <- mapM getExternalName $ dataConUnivAndExTyCoVars (orig k)
--   let res = Inj x (d <$ k) (Var <$> univ)
--   return $ Forall univ (foldr (:=>) res args'')

-- -- Extract a constructor's type with tyvars instantiated
-- -- We assume there are no existentially quantified tyvars
-- fromCoreConsInst :: DataCon -> [Type] -> InferM Type
-- fromCoreConsInst k tyargs = do
--   let d = dataConTyCon (orig k)
--   x <- fresh
--   args <- mapM fromCore $ dataConOrigArgTys (orig k)
--   -- Unroll datatype
--   -- u <- asks unrollDataTypes
--   -- let args' = if u then fmap (increaseLevel d) args else args
--   let args' = fmap (increaseLevel d) args
--   -- Instantiate and inject
--   let args'' = fmap (inj x . inst) args'
--   -- Rebuild type
--   let res = Inj x (d <$ k) tyargs
--   return $ foldr (:=>) res (reverse args'')
--   where
--     inst :: Type -> Type
--     inst t = foldr (uncurry subTyVar) t (zip (fmap getName $ dataConUnivAndExTyCoVars $ orig k) tyargs)

-- Lookup constrained variable emit its constraints
getVar :: Var -> InferM Scheme
getVar v =
  asks (M.lookup (getName v) . varEnv) >>= \case
    Just scheme -> do
      -- Localise constraints
      fre_scheme <-
        foldM
          ( \s x -> do
              y <- fresh
              return (rename x y s)
          )
          (scheme {boundvs = []})
          (boundvs scheme)
      case Scheme.constraints fre_scheme of
        Nothing ->
          return fre_scheme {Scheme.constraints = Nothing}
        Just var_cg -> do
          --- Emit constriants associated with a variable
          g <- asks branchGuard
          modify (\s -> s {InferM.constraints = InferM.constraints s <> guardWith g var_cg})
          return fre_scheme {Scheme.constraints = Nothing}
    Nothing -> do
      var_scheme <- fromCoreScheme $ varType v
      maximise True (body var_scheme)
      return var_scheme

-- Maximise/minimise a library type, i.e. assert every constructor occurs in covariant positions
maximise :: Bool -> Type -> InferM ()
maximise True (Data (Inj x d) _) = do
  l <- asks inferLoc
  mapM_ (\k -> emit (Con (getName k) l) (Dom (Inj x (getName d)))) $ tyConDataCons d
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()
