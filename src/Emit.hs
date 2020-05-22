{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Emit
  ( emitSetConstraint,
    emitTypeConstraint,
    getVar,
  )
where

import ConGraph
import Constraints
import Control.Monad.Except
import Control.Monad.RWS hiding (guard)
import qualified Data.List as L
import qualified Data.Map as M
import DataTypes
import FromCore
import GhcPlugins hiding (Expr (..), Type, empty)
import InferM
import Scheme
import Types

emitSetConstraint :: Monad m => K l -> K r -> DataType TyCon -> InferM s m ()
emitSetConstraint k1 k2 d
  | not (trivial $ orig d) =
    case toAtomic k1 k2 of
      Nothing -> do
        l <- asks inferLoc
        pprPanic "unsatisfiable cosntraint" (ppr (d, k1, k2, l))
      Just cs -> do
        cg <- gets congraph
        g <- asks branchGuard
        cg' <- foldM (\cg' (k1, k2) -> insert k1 k2 g (getName <$> d) cg') cg cs
        modify (\s -> s {congraph = cg'})
  | otherwise = return ()

emitTypeConstraint :: Monad m => Type T -> Type T -> InferM s m ()
emitTypeConstraint (Var _) (Var _) = return ()
emitTypeConstraint Ambiguous _ = return ()
emitTypeConstraint _ Ambiguous = return ()
emitTypeConstraint t1 t2
  | shape t1 /= shape t2 = do
    l <- asks inferLoc
    pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
emitTypeConstraint (t11 :=> t12) (t21 :=> t22) =
  emitTypeConstraint t21 t11 >> emitTypeConstraint t12 t22
emitTypeConstraint (Inj x d as) (Inj y d' _)
  | x /= y = do
    merge x y d d'
    emitSetConstraint (Dom x) (Dom y) (d {level = max (level d) (level d')})
    slice x y d as
emitTypeConstraint _ _ = return ()

-- Lookup constrained variable emit its constraints
getVar :: Monad m => Var -> InferM s m (Scheme s)
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
        Nothing -> return fre_scheme
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
maximise :: Monad m => Bool -> Type T -> InferM s m ()
maximise True (Inj x d _) = do
  l <- asks inferLoc
  mapM_ (\k -> emitSetConstraint (Con (getName k) l) (Dom x) d) $ tyConDataCons (orig d)
maximise b (x :=> y) = maximise (not b) x >> maximise b y
maximise _ _ = return ()

merge :: Monad m => RVar -> RVar -> DataType TyCon -> DataType TyCon -> InferM s m ()
merge x y xd yd
  | xd == yd = return ()
  | otherwise = do
    cg <- gets congraph
    cg' <- mergeLevel x y (fmap getName xd) (fmap getName yd) cg
    modify (\s -> s {congraph = cg'})

-- Take the slice of a datatype including parity
slice :: Monad m => Int -> Int -> DataType TyCon -> [Type S] -> InferM s m ()
slice x y d as = () <$ loop [] True d as
  where
    loop :: Monad m => [TyCon] -> Bool -> DataType TyCon -> [Type S] -> InferM s m [TyCon]
    loop ds p d as
      | trivial (orig d) || orig d `elem` ds = return ds
      | otherwise = do
        c <- asks allowContra
        foldM
          ( \ds' k ->
              ( if c
                  then branch' [k] x d -- If contraviarnt consturctors are permitted slices need to be guarded
                  else id
              )
                $ do
                  k_ty <- fromCoreConsInst (k <$ d) as
                  foldM (`step` p) ds' (fst $ decompTy k_ty)
          )
          ds
          (tyConDataCons $ orig d)
    step :: Monad m => [TyCon] -> Bool -> Type T -> InferM s m [TyCon]
    step ds p (Inj _ d' as') = do
      if p
        then emitSetConstraint (Dom x) (Dom y) d'
        else emitSetConstraint (Dom y) (Dom x) d'
      loop (orig d' : ds) p d' as'
    step ds p (a :=> b) = do
      ds' <- step ds (not p) a
      step ds' p b
    step ds _ _ = return ds
