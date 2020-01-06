{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TupleSections #-}

module InferM (
  InferM,
  runInferM,
  safeVar,
  withVar,
  withVar',
  withVars,
  withVars',
  withBranch,
  pushCase,
  popCase,
  topLevel,
  emitS,
  emitT,
  restrict
) where

import Prelude hiding (lookup)

import Control.Monad.Identity
import Control.Applicative

import qualified Data.List as L
import qualified Data.Map as M

import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr

import Utils
import Types
import Constraint

-- The environement variables and their types
type Context = M.Map Core.Name ([Int], ConSet, Type T)

-- The inference monad with all the bells and whistles
newtype InferM m a = InferM {
            -- gamma     stack            fresh  cs          (stack,         fresh, cs,    a)
  unInferM :: Context -> [Core.Unique] -> Int -> ConSet -> m ([Core.Unique], Int,   ConSet, a)
}

runInferM :: Monad m => InferM m a -> Context -> m a
runInferM m g = do
  (_, _, _, a) <- unInferM m g [] 0 M.empty
  return a

instance Functor m => Functor (InferM m) where
    fmap func m = InferM $ \gamma stack fresh cs -> (\(stack', fresh', cs', a) -> (stack', fresh', cs', func a)) <$> unInferM m gamma stack fresh cs
    {-# INLINE fmap #-}

instance (Functor m, Monad m) => Applicative (InferM m) where
    pure a = InferM $ \_ stack fresh cs -> return (stack, fresh, cs, a)
    {-# INLINE pure #-}

    InferM mf <*> InferM mx = InferM $ \gamma stack fresh cs -> do
        (stack', fresh',  cs', f)     <- mf gamma stack fresh cs
        (stack'', fresh'', cs'', a) <- mx gamma stack' fresh' cs'
        return (stack'', fresh'', cs'', f a)
    {-# INLINE (<*>) #-}

instance Monad m => Monad (InferM m) where
    return a = InferM $ \ _ stack fresh cs -> return (stack, fresh, cs, a)
    {-# INLINE return #-}

    m >>= k = InferM $ \gamma stack fresh cs -> do
        ~(stack', fresh', cs', a)  <- unInferM m gamma stack fresh cs
        ~(stack'', fresh'', cs'', b) <- unInferM (k a) gamma stack' fresh' cs'
        return (stack'', fresh'', cs' `M.union` cs'', b)
    {-# INLINE (>>=) #-}

instance FromCore T where
  type MT T = InferM
  dataType t = InferM $ \_ stack fresh cs -> return (stack, fresh + 1, cs, Inj fresh t)

-- Enter a new case statement
pushCase :: Monad m => Core.Expr Core.Var -> InferM m ()
pushCase (Core.Var (Core.getUnique -> s)) = InferM $ \_ stack fresh cs -> return (s:stack, fresh, cs, ())
pushCase _ = error "Cannot pattern match on a non-variable!"
 
-- Exit a case statement
popCase :: Monad m => InferM m ()
popCase = InferM $ \_ (s:stack) fresh cs -> return (stack, fresh, cs, ())
 
-- Is the current case statement at the top level
topLevel :: Monad m => Core.Expr Core.Var -> InferM m Bool
topLevel (Core.Var (Core.getUnique -> s)) = InferM $ \_ stack fresh cs -> return (stack, fresh, cs, s `notElem` stack)
topLevel _ = error "Cannot pattern match on a non-variable!"

-- Extract a variable from (local/global) context
safeVar :: Monad m => Core.Var -> InferM m (Type T)
safeVar v = get >>= safeVar'
  where
    get = InferM $ \gamma stack fresh cs -> return (stack, fresh, cs, gamma)

    safeVar' gamma = 
      case gamma M.!? Core.getName v of
        Just (xs, cs, ts) -> do
          -- Localise constraints
          ys <- mapM (\x -> InferM $ \_ stack fresh cs -> return (stack, fresh + 1, cs, fresh)) xs
          emitCS $ foldr (uncurry rename) cs (zip xs ys)
          return $ foldr (uncurry rename) ts (zip xs ys)

        Nothing ->
          -- We can assume the variable is in scope as GHC hasn't emitted a warning
          -- Assume all externally defined terms are unrefined
         fromCore $ Core.varType v

-- Add variable to scope
withVar :: Monad m => Core.Name -> [Int] -> ConSet -> Type T -> InferM m a -> InferM m a
withVar v xs' cs' t m = InferM $ \gamma stack fresh cs -> unInferM m (M.insert v (xs', cs', t) gamma) stack fresh cs

-- Add variables to scope
withVars :: Monad m => [(Core.Name, ([Int], ConSet, Type T))] -> InferM m a -> InferM m a
withVars vs m = InferM $ \gamma stack fresh cs -> unInferM m (foldr (\(a, (b, c, d)) -> M.insert a (b, c, d)) gamma vs) stack fresh cs

-- Add variable to scope
withVar' :: Monad m => Core.Name -> Type T -> InferM m a -> InferM m a
withVar' v t m = InferM $ \gamma stack fresh cs -> unInferM m (M.insert v ([], M.empty, t) gamma) stack fresh cs

-- Add variables to scope
withVars' :: Monad m => [(Core.Name, Type T)] -> InferM m a -> InferM m a
withVars' vs m = InferM $ \gamma stack fresh cs -> unInferM m (foldr (\(a, d) -> M.insert a ([], M.empty, d)) gamma vs) stack fresh cs

-- Map a function to constrants locally
withBranch :: Monad m => (ConSet -> ConSet) -> InferM m a -> InferM m a
withBranch f m = InferM $ \gamma stack fresh cs -> do {(stack, fresh, cs, a) <- unInferM m gamma stack fresh cs; return (stack, fresh, f cs, a)}

-- Emit a new subset constraint
emitS :: Monad m => K -> K -> InferM m ()
emitS k1 k2 = InferM $ \gamma stack fresh cs -> return (stack, fresh, insertS k1 k2 M.empty cs, ())

-- Emit a new subtype constraint
emitT :: Monad m => Type T -> Type T -> Core.Expr Core.Var -> InferM m ()
emitT t1 t2 e = InferM $ \gamma stack fresh cs -> return (stack, fresh, insertT t1 t2 M.empty cs e, ())

-- Emit a set of guarded contsraints
emitCS :: Monad m => ConSet -> InferM m ()
emitCS c = InferM $ \gamma stack fresh cs -> return (stack, fresh, c `M.union` cs, ())

-- Clear constraints and attach them to variables
restrict :: Monad m => [Type T] -> InferM m [([Int], ConSet, Type T)]
restrict ts = get >>= (return . restrict')
  where
    xs :: [Int]
    xs = concatMap domain ts

    get :: Monad m => InferM m ConSet
    get = InferM $ \gamma stack fresh cs -> return (stack, fresh, M.empty, cs)

    restrict' :: ConSet -> [([Int], ConSet, Type T)]
    restrict' cs = fmap (domain cs', cs',) ts
      where
        cs' = filterToSet xs $ resolve cs
