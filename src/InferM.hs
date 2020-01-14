{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module InferM (
  TypeScheme(..),

  InferM,
  runInferM,

  fetchStack,
  pushCase,
  popCase,
  topLevel,

  branch,
  branchAlts,

  getVar,
  putVar,
  putVars,

  emit,
  emitSubType,
  restrict,
) where

import Prelude hiding ((<>))

import qualified Data.Map as M

import Outputable hiding (empty)
import qualified GhcPlugins as Core hiding (empty)

import Types
import Constraint

-- A type quantified by constraints
newtype TypeScheme = TypeScheme ([Int], ConSet, Type T)

instance Outputable TypeScheme where
  ppr (TypeScheme (xs, cs, t)) = hang (text "forall" <+> fsep (map ppr xs) <> dot <> ppr t)
                                    2 (hang (text "where") 2 (ppr cs))

-- The environement variables and their types
type Context = M.Map Core.Name TypeScheme

-- The inference monad with all the bells and whistles
-- Essentially an unrolled RWST
newtype InferM m a = InferM {
            --environment  case stack              fresh  constraints (case stack,           fresh, cs,     ret)
  unInferM :: Context  ->  [Core.Expr Core.Var] -> Int -> ConSet -> m ([Core.Expr Core.Var], Int,   ConSet, a  )
}

runInferM :: Monad m => InferM m a -> Context -> m a
runInferM m g = do
  (_, _, _, a) <- unInferM m g [] 0 empty
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
        return (stack'', fresh'', cs'', b)
    {-# INLINE (>>=) #-}

instance Monad m => FromCore (InferM m) T where
  dataType d = (\x -> Inj x d) <$> fresh

-- A unique integer
fresh :: Monad m => InferM m Int
fresh = InferM $ \_ stack fresh cs -> return (stack, fresh + 1, cs, fresh) 

-- For debugging
fetchStack :: Monad m => InferM m [Core.Expr Core.Var]
fetchStack = InferM $ \_ stack fresh cs -> return (stack, fresh, cs, stack)

-- Enter a new case statement
pushCase :: Monad m => Core.Expr Core.Var -> InferM m ()
pushCase s = InferM $ \_ stack fresh cs -> return (s:stack, fresh, cs, ())
 
-- Exit a case statement
popCase :: Monad m => InferM m ()
popCase = InferM $ \_ (s:stack) fresh cs -> return (stack, fresh, cs, ())
 
-- Is the current case statement at the top level?
topLevel :: Monad m => Core.Expr Core.Var -> InferM m Bool
topLevel s = InferM $ \_ stack fresh cs -> return (stack, fresh, cs, inStack s stack)
  where
    inStack s [] = True
    inStack s (s':ss)
      -- Not very accurate!
      | Core.cheapEqExpr s s' = False
      | otherwise             = inStack s ss

-- Guard local constraints
branch :: Monad m => Core.Name -> Int -> Core.Name -> InferM m a -> InferM m a
branch k x d m = InferM $ \gamma stack fresh cs -> do 
    (stack', fresh', cs', a) <- unInferM m gamma stack fresh cs
    return (stack', fresh', guardWith k x d cs', a)

-- Guard local constraints with one of several possible branches
branchAlts :: Monad m => [Guard] -> InferM m a -> InferM m a
branchAlts gs m = InferM $ \gamma stack fresh cs -> do 
    (stack', fresh', cs', a) <- unInferM m gamma stack fresh cs
    return (stack', fresh', guardAlts gs cs', a)

-- Extract a variable from the environment
getVar :: Monad m => Core.Var -> Core.Expr Core.Var -> InferM m (Type T)
getVar v e = getCtx >>= getVar'
  where
    getCtx :: Monad m => InferM m Context
    getCtx = InferM $ \gamma stack fresh cs -> return (stack, fresh, cs, gamma)

    getVar' :: Monad m => Context -> InferM m (Type T)
    getVar' gamma = 
      case gamma M.!? Core.getName v of
        Just (TypeScheme (xs, cs, u)) -> do
          -- Localise constraints
          ys <- mapM (\x -> (x,) <$> fresh) xs
          emit   $ foldr (uncurry rename) cs ys
            
          let u' = foldr (uncurry rename) u ys
          v' <- fromCore $ Core.varType v
          emitSubType u' v' e

          return v'

        Nothing ->
          -- We can assume the variable is in scope as GHC hasn't emitted a warning
          -- Assume all externally defined terms are unrefined
         fromCore $ Core.varType v

-- Insert variables into the environment
putVar :: Core.Name -> TypeScheme -> InferM m a -> InferM m a
putVar n t m = InferM $ \gamma -> unInferM m (M.insert n t gamma)

-- Insert many variables
putVars :: [(Core.Name, TypeScheme)] -> InferM m a -> InferM m a
putVars vs m = InferM $ \gamma -> unInferM m (foldr (\(n, t) -> M.insert n t) gamma vs)

-- Emit a constraint set to the environment
emit :: Monad m => ConSet -> InferM m ()
emit cs = InferM $ \gamma stack fresh cs' -> return (stack, fresh, cs `union` cs', ())

-- Convert a subtyping constraint to a constraint set and emit
emitSubType :: Monad m => Type T -> Type T -> Core.Expr Core.Var -> InferM m ()
emitSubType (Forall a t1) (Forall b t2) e = emitSubType t1 (subTyVar b (Var a) t2) e
emitSubType t1 t2 e 
  | shape t1 /= shape t2                  = Core.pprPanic "Types must refine the same sort!" (Core.ppr (t1, t2, e))
emitSubType (t11 :=> t12) (t21 :=> t22) e = emitSubType t21 t11 e >> emitSubType t12 t22 e
emitSubType (Inj x d) (Inj y _) e
  | x /= y = mapM_ (\(Core.getName -> n) -> emit (insert (Dom x n) (Dom y n) top empty)) $ slice [d]
emitSubType (App t11 t12) (App t21 t22) e
  | refiableTyFunc t11                    = emitSubType t11 t21 e >> emitSubType t12 t22 e
emitSubType _ _ _                         = return ()

-- Clear constraints and attach them to variables
restrict :: Monad m => [(Core.Name, Type T)] -> InferM m [(Core.Name, TypeScheme)]
restrict ts = restrict' <$> getCs
  where
    getCs :: Monad m => InferM m ConSet
    getCs = InferM $ \gamma stack fresh cs -> return (stack, fresh, empty, cs)

    restrict' :: ConSet -> [(Core.Name, TypeScheme)]
    restrict' cs = fmap (\(x, t) -> (x, TypeScheme (domain cs', cs', t))) ts
      where
        xs  = concatMap (domain . snd) ts
        cs' = cs -- resolve xs cs