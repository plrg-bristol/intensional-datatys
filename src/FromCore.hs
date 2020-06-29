{-# LANGUAGE LambdaCase #-}

module FromCore
  ( freshCoreType,
    freshCoreScheme,
    fromCoreCons,
    consInstArgs,
    getVar,
  )
where

import Constraints
import Constructors
import Control.Monad.RWS
import qualified Data.Map as M
import GhcPlugins hiding ((<>), Expr (..), Type)
import InferM
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import Types

-- A fresh monomorphic type
freshCoreType :: Tcr.Type -> InferM Type
freshCoreType = fromCore Nothing

-- A fresh polymorphic type
freshCoreScheme :: Tcr.Type -> InferM Scheme
freshCoreScheme = fromCoreScheme Nothing

-- The type of a constructor injected into a fresh refinement environment
fromCoreCons :: DataCon -> InferM Scheme
fromCoreCons k = do
  x <- fresh
  let d = dataConTyCon k
  unless (trivial d) $ do
    l <- asks inferLoc
    emit (Con (getName k) l) (Dom (Inj x (getName d)))
  fromCoreScheme (Just x) (dataConUserType k)

-- The argument types of an instantiated constructor
consInstArgs :: RVar -> [Type] -> DataCon -> [Type]
consInstArgs x as k = fmap fromCoreInst (dataConRepArgTys k)
  where
    fromCoreInst :: Tcr.Type -> Type
    fromCoreInst (Tcr.TyVarTy a) =
      case lookup a (zip (dataConUnivTyVars k) as) of
        Nothing -> pprPanic "Type arguments aren't fully instantiated!" (ppr a)
        Just t -> t
    fromCoreInst (Tcr.AppTy a b) = App (fromCoreInst a) (fromCoreInst b)
    fromCoreInst (Tcr.TyConApp d as')
      | isTypeSynonymTyCon d,
        Just (as'', s) <- synTyConDefn_maybe d =
        fromCoreInst (substTy (extendTvSubstList emptySubst (zip as'' as')) s) -- Instantiate type synonym arguments
      | isClassTyCon d = Ambiguous -- Disregard type class evidence
      | trivial d = Data (Base d) (fmap fromCoreInst as') -- Datatypes with only one constructor
      | otherwise = Data (Inj x d) (fmap fromCoreInst as')
    fromCoreInst (Tcr.FunTy a b) = fromCoreInst a :=> fromCoreInst b
    fromCoreInst (Tcr.LitTy l) = Lit $ toIfaceTyLit l
    fromCoreInst _ = Ambiguous

-- Convert a monomorphic core type
fromCore :: Maybe RVar -> Tcr.Type -> InferM Type
fromCore _ (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore f (Tcr.AppTy a b) = liftM2 App (fromCore f a) (fromCore f b)
fromCore f (Tcr.TyConApp d as)
  | isTypeSynonymTyCon d,
    Just (as', s) <- synTyConDefn_maybe d =
    fromCore f (substTy (extendTvSubstList emptySubst (zip as' as)) s) -- Instantiate type synonyms
  | isClassTyCon d = return Ambiguous -- Disregard type class evidence
  | trivial d = Data (Base d) <$> mapM (fromCore f) as -- Datatypes with only one constructor
fromCore Nothing (Tcr.TyConApp d as) = do
  x <- fresh
  Data (Inj x d) <$> mapM (fromCore Nothing) as
fromCore (Just x) (Tcr.TyConApp d as) = Data (Inj x d) <$> mapM (fromCore (Just x)) as
fromCore f (Tcr.FunTy a b) = liftM2 (:=>) (fromCore f a) (fromCore f b)
fromCore _ (Tcr.LitTy l) = return $ Lit $ toIfaceTyLit l
fromCore _ _ = return Ambiguous -- Higher-ranked or impredicative types, casts and coercions

-- Convert a polymorphic core type
fromCoreScheme :: Maybe RVar -> Tcr.Type -> InferM Scheme
fromCoreScheme f (Tcr.ForAllTy b t) = do
  a <- getExternalName (Tcr.binderVar b)
  scheme <- fromCoreScheme f t
  return scheme {tyvars = a : tyvars scheme}
fromCoreScheme f (Tcr.FunTy a b) = do
  a' <- fromCore f a
  scheme <- fromCoreScheme f b -- Optimistically push arrows inside univiersal quantifier
  return scheme {body = a' :=> body scheme}
fromCoreScheme f t = Forall [] <$> fromCore f t

-- Lookup constrained variable and emit its constraints
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
      -- Emit constriants associated with a variable
      g <- asks branchGuard
      modify (\s -> s {InferM.constraints = InferM.constraints s <> guardWith g (Scheme.constraints fre_scheme)})
      return fre_scheme {Scheme.constraints = mempty}
    Nothing -> do
      var_scheme <- freshCoreScheme $ varType v
      maximise True (body var_scheme)
      return var_scheme

-- Maximise/minimise a library type, i.e. assert every constructor occurs in covariant positions
maximise :: Bool -> Type -> InferM ()
maximise True (Data (Inj x d) _) = do
  l <- asks inferLoc
  mapM_ (\k -> emit (Con (getName k) l) (Dom (Inj x (getName d)))) $ tyConDataCons d
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()
