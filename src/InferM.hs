{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module InferM (
  InferM,
  runInferM,

  pushCase,
  popCase,
  topLevel,

  branch,

  getVar,
  putVar,

  emit,
  emitSubType,
  restrict,
) where

import qualified Data.List as L
import qualified Data.Map as M

import qualified GhcPlugins as Core

import Types
import Constraint

-- The environement variables and their types
type Context = M.Map Core.Name TypeScheme

-- The inference monad with all the bells and whistles
newtype InferM m a = InferM {
            -- gamma     stack            fresh  cs          (stack,         fresh, cs,     a)
  unInferM :: Context -> [Core.Unique] -> Int -> ConSet -> m ([Core.Unique], Int,   ConSet, a)
}

runInferM :: Monad m => InferM m a -> Context -> m a
runInferM m g = do
  (_, _, _, a) <- unInferM m g [] 0 mempty
  return a

instance Functor m => Functor (InferM m) where
    fmap func m = InferM $ \gamma stack fresh cs -> (\(stack', fresh', cs', a) -> (stack', fresh', cs', func a)) <$> unInferM m gamma stack fresh cs
    {-# INLINE fmap #-}

instance (Functor m, Monad m) => Applicative (InferM m) where
    pure a = InferM $ \_ stack fresh cs -> return (stack, fresh, cs, a)
    {-# INLINE pure #-}

    InferM mf <*> InferM mx = InferM $ \gamma stack fresh cs -> do
        (stack', fresh',  cs', f)   <- mf gamma stack fresh cs
        (stack'', fresh'', cs'', a) <- mx gamma stack' fresh' cs'
        return (stack'', fresh'', cs'', f a)
    {-# INLINE (<*>) #-}

instance Monad m => Monad (InferM m) where
    return a = InferM $ \ _ stack fresh cs -> return (stack, fresh, cs, a)
    {-# INLINE return #-}

    m >>= k = InferM $ \gamma stack fresh cs -> do
        ~(stack', fresh', cs', a)    <- unInferM m gamma stack fresh cs
        ~(stack'', fresh'', cs'', b) <- unInferM (k a) gamma stack' fresh' cs'
        return (stack'', fresh'', cs' <> cs'', b)
    {-# INLINE (>>=) #-}

instance Monad m => FromCore (InferM m) T where
  dataType d = (`Inj` d) <$> fresh

fresh :: Monad m => InferM m Int
fresh = InferM $ \_ stack fresh cs -> return (stack, fresh + 1, cs, fresh) 

-- Enter a new case statement
pushCase :: Monad m => Core.Expr Core.Var -> InferM m ()
pushCase (Core.Var (Core.getUnique -> s)) = InferM $ \_ stack fresh cs -> return (s:stack, fresh, cs, ())
pushCase _ = error "Cannot pattern match on a non-variable!"
 
-- Exit a case statement
popCase :: Monad m => InferM m ()
popCase = InferM $ \_ (s:stack) fresh cs -> return (stack, fresh, cs, ())
 
-- Is the current case statement at the top level?
topLevel :: Monad m => Core.Expr Core.Var -> InferM m Bool
topLevel (Core.Var (Core.getUnique -> s)) = InferM $ \_ stack fresh cs -> return (stack, fresh, cs, s `notElem` stack)
topLevel _ = error "Cannot pattern match on a non-variable!"

-- Guard local constraints
branch :: Monad m => Core.Name -> Int -> Core.Name -> InferM m a -> InferM m a
branch k x d m = InferM $ \gamma stack fresh cs -> do 
    (stack, fresh, cs, a) <- unInferM m gamma stack fresh cs
    return (stack, fresh, guardWith k x d cs, a)

-- Extract a variable from the environment
getVar :: Monad m => Core.Var -> InferM m (Type T)
getVar v = getCtx >>= getVar'
  where
    getCtx :: Monad m => InferM m Context
    getCtx = InferM $ \gamma stack fresh cs -> return (stack, fresh, cs, gamma)

    getVar' :: Monad m => Context -> InferM m (Type T)
    getVar' gamma = 
      case gamma M.!? Core.getName v of
        Just (TypeScheme (xs, cs, ts)) -> do
          -- Localise constraints
          ys <- mapM (\x -> (x,) <$> fresh) xs
          emit $ foldr (uncurry rename) cs ys
          return $ foldr (uncurry rename) ts ys

        Nothing ->
          -- We can assume the variable is in scope as GHC hasn't emitted a warning
          -- Assume all externally defined terms are unrefined
         fromCore $ Core.varType v

-- Insert variables into the environment
putVar :: [(Core.Name, TypeScheme)] -> InferM m a -> InferM m a
putVar vs m = InferM $ \gamma -> unInferM m (M.fromList vs `M.union` gamma)

-- Emit a constraint set to the environment
emit :: Monad m => ConSet -> InferM m ()
emit cs = InferM $ \gamma stack fresh cs' -> return (stack, fresh, cs <> cs', ())

-- Convert a subtyping constraint to a constraint set and emit
emitSubType :: Monad m => Type T -> Type T -> Core.Expr Core.Var -> InferM m ()
emitSubType t1 t2 e 
  | shape t1 /= shape t2                  = Core.pprPanic "Types must refine the same sort!" (Core.ppr (t1, t2, e))
emitSubType (t11 :=> t12) (t21 :=> t22) e = emitSubType t21 t11 e >> emitSubType t12 t22 e
emitSubType (Inj x d) (Inj y _) e 
  | x /= y                                = mapM_ (\(Core.getName -> n) -> emit (singleton (Dom x n) (Dom y n) mempty)) $ slice [d]
emitSubType (Forall _ t1) (Forall _ t2) e = emitSubType t1 t2 e
emitSubType _ _ _                         = return ()

-- Clear constraints and attach them to variables
restrict :: Monad m => [(Core.Name, Type T)] -> InferM m [(Core.Name, TypeScheme)]
restrict ts = restrict' <$> get
  where
    get :: Monad m => InferM m ConSet
    get = InferM $ \gamma stack fresh cs -> return (stack, fresh, mempty, cs)

    restrict' :: ConSet -> [(Core.Name, TypeScheme)]
    restrict' cs = fmap (\(x, t) -> (x, TypeScheme (domain cs', cs', t))) ts
      where
        cs' = cs -- resolve xs cs
        xs  = concatMap (domain . snd) ts