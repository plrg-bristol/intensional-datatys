{-# LANGUAGE LambdaCase #-}

module Intensional.FromCore
  ( freshCoreType,
    freshCoreScheme,
    fromCoreCons,
    consInstArgs,
    getVar,
  )
where

import Intensional.Constraints
import Intensional.Constructors
import Control.Monad.RWS
import qualified Data.IntSet as I
import qualified Data.Map as M
import GhcPlugins hiding ((<>), Expr (..), Type)
import Intensional.InferM
import Intensional.Scheme as Scheme
import ToIface
import qualified TyCoRep as Tcr
import Intensional.Types

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
  b <- isIneligible d
  unless b $ do
    l <- asks inferLoc
    emitKD k l (Inj x d)
  fromCoreScheme (Just x) (dataConUserType k)

-- The argument types of an instantiated constructor
consInstArgs :: RVar -> [Type] -> DataCon -> InferM [Type]
consInstArgs x as k = mapM fromCoreInst (dataConRepArgTys k)
  where
    fromCoreInst :: Tcr.Type -> InferM Type
    fromCoreInst (Tcr.TyVarTy a) =
      case lookup a (zip (dataConUnivTyVars k) as) of
        Nothing -> return (Var (getName a))
        Just t -> return t
    fromCoreInst (Tcr.AppTy a b) = App <$> (fromCoreInst a) <*> (fromCoreInst b)
    fromCoreInst (Tcr.TyConApp d as')
      | isTypeSynonymTyCon d,
        Just (as'', s) <- synTyConDefn_maybe d =
        fromCoreInst (substTy (extendTvSubstList emptySubst (zip as'' as')) s) -- Instantiate type synonym arguments
      | isClassTyCon d = return Ambiguous -- Disregard type class evidence
      | otherwise =
          do  b <- isIneligible d
              if b then Data (Base d) <$> (mapM fromCoreInst as') 
                   else Data (Inj x d) <$> (mapM fromCoreInst as')
    fromCoreInst (Tcr.FunTy a b) = (:=>) <$> fromCoreInst a <*> fromCoreInst b
    fromCoreInst (Tcr.LitTy l) = return (Lit $ toIfaceTyLit l)
    fromCoreInst _ = return Ambiguous

-- Convert a monomorphic core type
fromCore :: Maybe RVar -> Tcr.Type -> InferM Type
fromCore _ (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore f (Tcr.AppTy a b) = liftM2 App (fromCore f a) (fromCore f b)
fromCore f (Tcr.TyConApp d as)
  | isTypeSynonymTyCon d,
    Just (as', s) <- synTyConDefn_maybe d =
    fromCore f (substTy (extendTvSubstList emptySubst (zip as' as)) s) -- Instantiate type synonyms
  | isClassTyCon d = return Ambiguous -- Disregard type class evidence
fromCore Nothing (Tcr.TyConApp d as) = do
  x <- fresh
  b <- isIneligible d
  if b then
    Data (Base d) <$> mapM (fromCore Nothing) as
  else
    Data (Inj x d) <$> mapM (fromCore Nothing) as
fromCore (Just x) (Tcr.TyConApp d as) = do
  b <- isIneligible d
  if b then
    Data (Base d) <$> mapM (fromCore (Just x)) as
  else
    Data (Inj x d) <$> mapM (fromCore (Just x)) as
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
          (scheme {boundvs = mempty})
          (I.toList (boundvs scheme))
      -- Emit constriants associated with a variable
      g <- asks branchGuard
      tell (guardWith g (constraints fre_scheme))
      return fre_scheme {Scheme.constraints = mempty}
    Nothing -> do
      var_scheme <- freshCoreScheme $ varType v
      maximise True (body var_scheme)
      return var_scheme

-- Maximise/minimise a library type, i.e. assert every constructor occurs in covariant positions
maximise :: Bool -> Type -> InferM ()
maximise True (Data (Inj x d) _) = do
  l <- asks inferLoc
  mapM_ (\k -> emitKD k l (Inj x d)) $ tyConDataCons d
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()
