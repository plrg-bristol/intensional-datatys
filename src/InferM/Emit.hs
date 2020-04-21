{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module InferM.Emit
  ( emit,
  )
where

import ConGraph
import Constraints
import Control.Monad
import qualified Data.Map as M
import Data.Maybe
import DataCon
import IfaceType
import InferM.FromCore
import InferM.Internal
import Name
import Outputable hiding (empty)
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import TyCon
import Types
import UniqSet
import Var
import Prelude hiding (max)

-- Variadic emittable constraints
class Emit t r where
  emit :: t -> r

instance (unit ~ (), Monad m) => Emit ConGraph (InferM m unit) where
  emit cg = InferM $ \_ _ _ p f f' cs -> return $ Right (p, f, f', cg `union` cs, ())

-- Emit non-atomic set constraint
instance (unit ~ (), Monad m) => Emit (K a) (K b -> DataType TyCon -> InferM m unit) where
  emit _ _ d | trivial (underlying d) = return ()
  emit k1 k2 d = InferM $ \_ _ l path fresh old_fresh cs ->
    case insert k1 k2 (getName <$> d) cs of
      Just cs' -> return $ Right (path, fresh, old_fresh, cs', ())
      Nothing -> return $ Left (Error "Invalid set constraint!" l k1 k2)

-- Emit k in X(d)
instance (unit ~ (), Monad m) => Emit DataCon (Int -> DataType TyCon -> InferM m unit) where
  emit _ _ d | trivial (underlying d) = return ()
  emit k x d = do
    l <- getLoc
    emit (Con (getName k) l) (Dom x) d

-- Emit X(d) < K
instance (unit ~ (), Monad m) => Emit Int (DataType TyCon -> [DataCon] -> InferM m unit) where
  emit _ d _ | trivial (underlying d) = return ()
  emit x d ks = do
    l <- getLoc
    emit (Dom x) (Set (mkUniqSet (getName <$> ks)) l) d

-- Emit Type < Type
instance (unit ~ (), Monad m) => Emit (Type T TyCon) (Type T TyCon -> InferM m unit) where
  emit (Var _) (Var _) = return ()
  emit Ambiguous _ = return ()
  emit _ Ambiguous = return ()
  emit t1 t2
    | shape t1 /= shape t2 = do
      l <- getLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
    emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y d' as')
    | x /= y = do
      when (d /= d') $
        -- Merge levels
        mergeLevel x (getName <$> d) y (getName <$> d')
      emit (Dom x) (Dom y) (max d d')
      slice x y d as
  emit _ _ = return ()

-- Emit Type < IType
instance (unit ~ (), Monad m) => Emit (Type T TyCon) (Type T IfaceTyCon -> InferM m unit) where
  emit (Var _) (Var _) = return ()
  emit Ambiguous _ = return ()
  emit _ Ambiguous = return ()
  emit t1 t2
    | shape (toIfaceTyCon <$> t1) /= shape t2 = do
      l <- getLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
    emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y d' as')
    | x /= y = do
      when ((toIfaceTyCon <$> d) /= d') $
        -- Merge levels
        mergeLevel x (getName <$> d) y (getName (underlying d) <$ d')
      emit (Dom x) (Dom y) (max d d')
      slice x y d as
  emit _ _ = return ()

-- Emit IType < Type
instance (unit ~ (), Monad m) => Emit (Type T IfaceTyCon) (Type T TyCon -> InferM m unit) where
  emit (Var _) (Var _) = return ()
  emit Ambiguous _ = return ()
  emit _ Ambiguous = return ()
  emit t1 t2
    | shape t1 /= shape (toIfaceTyCon <$> t2) = do
      l <- getLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
    emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y d' as')
    | x /= y = do
      when (d /= (toIfaceTyCon <$> d')) $
        -- Merge levels
        mergeLevel x (getName (underlying d') <$ d) y (getName <$> d')
      emit (Dom x) (Dom y) (max d' d)
      slice x y d' as'
  emit _ _ = return ()

-- Extract a variable from the environment and import constraints
instance (unit ~ Scheme TyCon, Monad m) => Emit Var (InferM m unit) where
  emit v = do
    may_scheme <- getVar v
    case may_scheme of
      Just scheme -> do
        -- Localise constraints
        fre_scheme <- foldM (\s x -> liftM2 (rename x) fresh $ return s) (scheme {boundvs = []}) (boundvs scheme)
        forM_ (constraints fre_scheme) emit
        return $ fre_scheme {constraints = Nothing}
      Nothing -> do
        -- Maximise library type
        var_scheme <- fromCoreScheme $ varType v
        maximise True (body var_scheme)
        return var_scheme

-- Get all datacons a fully applied variable might contain
varDataCons :: Var -> [DataCon]
varDataCons = dcs . resty . varType
  where
    resty (Tcr.ForAllTy _ t) = resty t
    resty (Tcr.FunTy _ t) = resty t
    resty t = t
    dcs (Tcr.TyConApp d' _) = tyConDataCons d'

-- Maximise/minimise a type
maximise :: Monad m => Bool -> Type T TyCon -> InferM m ()
maximise True (Inj x d _) = do
  l <- getLoc
  mapM_ (\k -> emit (Con (getName k) l) (Dom x) d) $ tyConDataCons (underlying d)
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()

-- Take the slice of a datatype including parity
slice :: Monad m => Int -> Int -> DataType TyCon -> [Type S TyCon] -> InferM m ()
slice x y = loop [] True
  where
    loop _ _ d _ | trivial (underlying d) = return ()
    loop ds p d as
      | underlying d `elem` ds = return ()
      | otherwise = do
        c <- allowContra
        if c
          then mapM_ (\k -> branch Nothing ([k] <$ d) x (fromCoreConsInst (k <$ d) as >>= (mapM_ (step ds p) . fst . decompTy))) (tyConDataCons $ underlying d)
          else mapM_ (\k -> fromCoreConsInst (k <$ d) as >>= (mapM_ (step ds p) . fst . decompTy)) (tyConDataCons $ underlying d)
    step ds p (Inj _ d' as') = do
      if p
        then emit (Dom x) (Dom y) d'
        else emit (Dom y) (Dom x) d'
      loop (underlying d' : ds) p d' as'
    step ds p (a :=> b) = step ds (not p) a >> step ds p b
    step _ _ _ = return ()

-- Copy constraints to a new level
mergeLevel :: Monad m => Int -> DataType Name -> Int -> DataType Name -> InferM m ()
mergeLevel x xd y yd = InferM $ \mod gamma occ_l path fresh old_fresh cg -> do
  let xps = getPreds x xd cg
  let cg'' = M.foldrWithKey (\xp g -> union $ guardDirect g (fromJust $ insert xp (Dom x) yd empty)) cg xps
  let yss = getSuccs y yd cg
  return $ Right (path, fresh, old_fresh, M.foldrWithKey (\ys g -> union $ guardDirect g (fromJust $ insert (Dom y) ys xd empty)) cg'' yss, ())
