{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Emit
  ( emit,
  )
where

import ConGraph
import Constraints
import Control.Lens
import Control.Monad.Except
import Control.Monad.RWS hiding (guard)
import qualified Data.List as L
import qualified Data.Map as M
import Data.Maybe
import DataTypes
import FromCore
import GhcPlugins hiding (Expr (..), Type, empty)
import Guards
import IfaceType
import InferM
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import Types

-- Variadic emittable constraints
class Emit t r where
  emit :: t -> r

-- Emit non-atomic set constraint
instance (unit ~ (), Monad m) => Emit (K a) (K b -> DataType TyCon -> InferM s m unit) where
  emit k1 k2 d
    | not (trivial $ underlying d) =
      case toAtomic k1 k2 of
        Nothing -> do
          l <- view inferLoc
          throwError $ Error (getName <$> d) k1 k2 l
        Just cs -> do
          cg <- use congraph
          g <- use branchGuard
          foldM (\cg' (k1, k2) -> insert k1 k2 g (getName <$> d) cg') cg cs >>= assign congraph
    | otherwise = return ()

-- Emit k in X(d)
instance (unit ~ (), Monad m) => Emit DataCon (Int -> DataType TyCon -> InferM s m unit) where
  emit k x d = do
    l <- view inferLoc
    emit (Con (getName k) l) (Dom x) d

-- Emit X(d) < K
instance (unit ~ (), Monad m) => Emit Int (DataType TyCon -> [DataCon] -> InferM s m unit) where
  emit x d ks = do
    l <- view inferLoc
    emit (Dom x) (Set (mkUniqSet (getName <$> ks)) l) d

-- Emit Type < Type
instance (unit ~ (), Monad m) => Emit (Type T TyCon) (Type T TyCon -> InferM s m unit) where
  emit (Var _) (Var _) = return ()
  emit Ambiguous _ = return ()
  emit _ Ambiguous = return ()
  emit t1 t2
    | shape t1 /= shape t2 = do
      l <- view inferLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
    emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y d' as')
    | x /= y = do
      merge x y d d'
      emit (Dom x) (Dom y) (deepest d d')
      slice x y d as
  emit _ _ = return ()

-- Emit Type < IType
instance (unit ~ (), Monad m) => Emit (Type T TyCon) (Type T IfaceTyCon -> InferM s m unit) where
  emit (Var _) (Var _) = return ()
  emit Ambiguous _ = return ()
  emit _ Ambiguous = return ()
  emit t1 t2
    | shape (toIfaceTyCon <$> t1) /= shape t2 = do
      l <- view inferLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
    emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y d' as')
    | x /= y = do
      merge x y d (underlying d <$ d')
      emit (Dom x) (Dom y) (deepest d d')
      slice x y d as
  emit _ _ = return ()

-- -- Emit IType < Type
instance (unit ~ (), Monad m) => Emit (Type T IfaceTyCon) (Type T TyCon -> InferM s m unit) where
  emit (Var _) (Var _) = return ()
  emit Ambiguous _ = return ()
  emit _ Ambiguous = return ()
  emit t1 t2
    | shape t1 /= shape (toIfaceTyCon <$> t2) = do
      l <- view inferLoc
      pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
  emit (t11 :=> t12) (t21 :=> t22) =
    emit t21 t11 >> emit t12 t22
  emit (Inj x d as) (Inj y d' as')
    | x /= y = do
      merge x y (underlying d' <$ d) d'
      emit (Dom x) (Dom y) (deepest d' d)
      slice x y d' as'
  emit _ _ = return ()

-- Extract a variable from the environment and import constraints
instance Monad m => Emit Var (InferM s m (Scheme TyCon (GuardSet s))) where
  emit v =
    views varEnv (getVar v) >>= \case
      Just scheme -> do
        -- Localise constraints
        xys <-
          mapM
            ( \x -> do
                y <- freshRVar <<+= 1
                return (x, y)
            )
            (L.sort $ boundvs scheme)
        fre_scheme <- renameAll xys scheme {boundvs = []}

        case constraints scheme of
          Nothing -> return fre_scheme
          Just cg -> do
            g <- use branchGuard
            cg' <- guardWith g cg
            congraph %= unionUniq cg'
            return fre_scheme {constraints = Nothing}
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
maximise :: Monad m => Bool -> Type T TyCon -> InferM s m ()
maximise True (Inj x d _) = do
  l <- view inferLoc
  mapM_ (\k -> emit (Con (getName k) l) (Dom x) d) $ tyConDataCons (underlying d)
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()

merge :: Monad m => RVar -> RVar -> DataType TyCon -> DataType TyCon -> InferM s m ()
merge x y xd yd
  | xd == yd = return ()
  | otherwise = do
    cg <- use congraph
    congraph <~ mergeLevel x y (fmap getName xd) (fmap getName yd) cg

-- Take the slice of a datatype including parity
slice :: Monad m => Int -> Int -> DataType TyCon -> [Type S TyCon] -> InferM s m ()
slice x y d as = () <$ loop [] True d as
  where
    loop :: Monad m => [TyCon] -> Bool -> DataType TyCon -> [Type S TyCon] -> InferM s m [TyCon]
    loop ds p d as
      | trivial (underlying d) || underlying d `elem` ds = return ds
      | otherwise = do
        c <- view allowContra

        foldM
          ( \ds k -> do
              g <- use branchGuard

              -- If contraviarnt consturctors are permitted slices need to be guarded
              unless c $
                branchGuard <~ do
                  b <- dom [getName k] x (getName <$> d)
                  g &&& b

              k_ty <- fromCoreConsInst (k <$ d) as
              ds' <- foldM (`step` p) ds (fst $ decompTy k_ty)

              -- Restore guard
              branchGuard .= g
              return ds'
          )
          ds
          (tyConDataCons $ underlying d)
    step :: Monad m => [TyCon] -> Bool -> Type T TyCon -> InferM s m [TyCon]
    step ds p (Inj _ d' as') = do
      if p
        then emit (Dom x) (Dom y) d'
        else emit (Dom y) (Dom x) d'
      loop (underlying d' : ds) p d' as'
    step ds p (a :=> b) = do
      ds' <- step ds (not p) a
      step ds' p b
    step ds _ _ = return ds
