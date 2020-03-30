{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Emit (
  emit,
) where

import Control.Monad

import Var
import Name
import TyCon
import UniqSet
import DataCon
import ToIface
import IfaceType
import Outputable
import qualified TyCoRep as Tcr

import Types
import Scheme
import ConGraph
import FromCore
import Constraints
import InferM.Internal

-- Variadic emittable constraints
class Emit t r where
  emit :: t -> r

instance (unit ~ (), Monad m) => Emit ConGraph (InferM m unit) where
  emit cg = InferM $ \_ _ _ p f cs -> return (p, f, cg `union` cs, ())

-- Emit non-atomic set constraint
instance (unit ~ (), Monad m) => Emit (K a) (K b -> Name -> InferM m unit) where
  emit k1 k2 d = InferM $ \_ _ l path fresh cs ->
    case insert k1 k2 d cs of
      Just cs' -> return (path, fresh, cs', ())
      Nothing  -> pprPanic "Invalid set constraint!" $ ppr (k1, k2, l)

-- Emit k in X(d)
instance (unit ~ (), Monad m) => Emit DataCon (Int -> TyCon -> InferM m unit) where
  emit k x d = do
    l <- getLoc
    emit (Con (getName k) l) (Dom x) $ getName d

-- Emit X(d) < K
instance (unit ~ (), Monad m) => Emit Int (TyCon -> [DataCon] -> InferM m unit) where
  emit x d ks = do
    l <- getLoc
    emit (Dom x) (Set (mkUniqSet (getName <$> ks)) l) $ getName d

-- Emit Type < Type
instance (unit ~ (), Monad m) => Emit (Type T TyCon) (Type T TyCon -> InferM m unit) where
  emit (Var _) (Var _)        = return ()
  emit Ambiguous _            = return ()
  emit _ Ambiguous            = return ()
  emit t1 t2
    | shape t1 /= shape t2 = do
      l <- getLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
      emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y _ as')
    | x /= y = do
      mapM_ (emit (Dom x) (Dom y) . getName) $ slice [d]
      mapM_ (uncurry emit) $ zip as as'
  emit _ _ = return ()

-- Emit Type < IType
instance (unit ~ (), Monad m) => Emit (Type T TyCon) (Type T IfaceTyCon -> InferM m unit) where
  emit (Var _) (Var _)        = return ()
  emit Ambiguous _            = return ()
  emit _ Ambiguous            = return ()
  emit t1 t2
    | shape (toIfaceTyCon <$> t1) /= shape t2 = do
      l <- getLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
      emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y _ as')
    | x /= y = do
      mapM_ (emit (Dom x) (Dom y) . getName) $ slice [d]
      mapM_ (uncurry emit) $ zip as as'
  emit _ _ = return ()

-- Emit IType < Type
instance (unit ~ (), Monad m) => Emit (Type T IfaceTyCon) (Type T TyCon -> InferM m unit) where
  emit (Var _) (Var _)        = return ()
  emit Ambiguous _            = return ()
  emit _ Ambiguous            = return ()
  emit t1 t2
    | shape t1 /= shape (toIfaceTyCon <$> t2) = do
      l <- getLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
      emit t21 t11 >> emit t12 t22
  emit (Inj x _ as) (Inj y d as')
    | x /= y = do
      mapM_ (emit (Dom x) (Dom y) . getName) $ slice [d]
      mapM_ (uncurry emit) $ zip as as'
  emit _ _ = return ()

-- Extract a variable from the environment and import constraints
instance (unit ~ Scheme TyCon, Monad m) => Emit Var (InferM m unit) where
  emit v = do
    var_scheme <- fromCoreScheme $ varType v
    may_scheme <- getVar $ getName v
    case may_scheme of
      Just scheme -> do
        -- Localise constraints
        fre_scheme <- foldM (\s x -> liftM2 (rename x) fresh $ return s) scheme (boundvs scheme)
        forM_ (constraints fre_scheme) emit
        emit (body fre_scheme) (body var_scheme)

      Nothing ->
        -- Maximise library type
        case decomp (body var_scheme) of
          (_, Inj x d _) -> do
            l <- getLoc
            mapM_ (\k -> emit (Con (getName k) l) (Dom x) $ getName d) $ varDataCons v
          _ -> return ()
    return var_scheme

-- Get all datacons a fully applied variable might contain
varDataCons :: Var -> [DataCon]
varDataCons = dcs . resty . varType
  where
    resty (Tcr.ForAllTy _ t) = resty t
    resty (Tcr.FunTy _ t)    = resty t
    resty t                  = t

    dcs (Tcr.TyConApp d' _)  = tyConDataCons d'

-- Take the slice of a datatype
slice :: [TyCon] -> [TyCon]
slice tcs
  | tcs' == tcs = tcs
  | otherwise   = slice tcs'
  where
    tcs' = [tc' | tc <- tcs
                , dc <- tyConDataCons tc
                , (Tcr.TyConApp tc' _) <- dataConOrigArgTys dc
                , tc' `notElem` tcs
                , refinable tc']
                ++ tcs

