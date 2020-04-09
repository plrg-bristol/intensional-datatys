{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Emit (
  emit,
) where

import Prelude hiding (sum, max)
import Control.Monad
import qualified Data.Map as M

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
instance (unit ~ (), Monad m) => Emit (K a) (K b -> DataType Name -> InferM m unit) where
  emit k1 k2 d = InferM $ \_ _ l path fresh cs ->
    case insert k1 k2 d cs of
      Just cs' -> return (path, fresh, cs', ())
      Nothing  -> pprPanic "Invalid set constraint!" $ ppr (k1, k2, l)

-- Emit k in X(d)
instance (unit ~ (), Monad m) => Emit DataCon (Int -> DataType TyCon -> InferM m unit) where
  emit k x d = do
    l <- getLoc
    emit (Con (getName k) l) (Dom x) $ fmap getName d

-- Emit X(d) < K
instance (unit ~ (), Monad m) => Emit Int (DataType TyCon -> [DataCon] -> InferM m unit) where
  emit x d ks = do
    l <- getLoc
    emit (Dom x) (Set (mkUniqSet (getName <$> ks)) l) $ fmap getName d

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
  emit (Inj x (b, d) as) (Inj y (b', d') as')
    | x /= y = do
      emit (Dom x) (Dom y) (b || b', getName d)
      slice x y d as
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
  emit (Inj x (b, d) as) (Inj y (b', d') as')
    | x /= y = do
      emit (Dom x) (Dom y) (b || b', getName d)
      slice x y d as
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
  emit (Inj x (b', d') as) (Inj y (b, d) as')
    | x /= y = do
      emit (Dom x) (Dom y) (b || b', getName d)
      slice x y d as'
  emit _ _ = return ()

-- Extract a variable from the environment and import constraints
instance (unit ~ Scheme TyCon, Monad m) => Emit Var (InferM m unit) where
  emit v = do
    may_scheme <- getVar v
    case may_scheme of
      Just scheme -> do
        -- Localise constraints
        fre_scheme <- foldM (\s x -> liftM2 (rename x) fresh $ return s) (scheme{ boundvs = [] }) (boundvs scheme)
        forM_ (constraints fre_scheme) emit
        return $ fre_scheme{ constraints = Nothing }

      Nothing -> do
        -- Maximise library type
        var_scheme <- fromCoreScheme [] $ varType v
        case decomp (body var_scheme) of
          (_, Inj x d _) -> do
            l <- getLoc
            mapM_ (\k -> emit (Con (getName k) l) (Dom x) $ fmap getName $ d) $ varDataCons v
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

-- Get constructors argis
-- Expand synonyms!
dataConArgs :: Monad m => TyCon -> [Type S TyCon] -> InferM m [(DataCon, [Type S TyCon])]
dataConArgs d as' = mapM (\k -> mapM (inst k) (dataConOrigArgTys k) >>= \args -> return (k, args)) $ tyConDataCons d
  where
    inst :: Monad m => DataCon -> Tcr.Type -> InferM m (Type S TyCon)
    inst k arg = do
      t <- fromCore [] arg
      as <- mapM getExternalName $ dataConUnivTyVars k
      return $ foldr (uncurry subTyVar) t (zip as as')

-- Take the slice of a datatype including parity
slice :: Monad m => Int -> Int -> TyCon -> [Type S TyCon] -> InferM m ()
slice x y = loop [] True
  where
    loop ds p d as
      | d `elem` ds = return ()
      | otherwise   = dataConArgs d as >>= mapM_ (\(k, args) -> branch Nothing [k] x False $ mapM_ (step (d:ds) p) args)

    -- If d has one constructor end here
    step ds p (Base d' as') = do
      if p
        then emit (Dom x) (Dom y) (d' `elem` ds, getName d')
        else emit (Dom y) (Dom x) (d' `elem` ds, getName d')
      loop ds p d' as'
    step ds p (a :=> b) = step ds (not p) a >> step ds p b
    step ds p _         = return ()
