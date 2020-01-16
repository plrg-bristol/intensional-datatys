{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module InferM (
  RefinedScheme(..),
  Context,

  InferM,
  runInferM,

  fetchStack,
  pushCase,
  popCase,
  topLevel,

  branch,
  -- branchAlts,

  getVar,
  putVar,
  putVars,

  emit,
  emitSingle,
  emitSubType,
  restrict,
) where

import Prelude hiding ((<>))

import Control.Monad

import qualified Data.List as L
import qualified Data.Map as M

import Outputable hiding (empty)
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core hiding (empty)

import Types
import Constraint

-- A type quantified by constraints
data RefinedScheme = RefinedScheme [Core.Name] [Int] ConSet (Type T)

instance Outputable RefinedScheme where
  ppr (RefinedScheme as xs cs t) = hang (text "forall" <+> fsep (map ppr as) <> dot <> text "forall" <+> fsep (map ppr xs) <> dot <> ppr t)
                                      2 (hang (text "where") 2 (ppr cs))

-- The environement variables and their types
type Context = M.Map Core.Name RefinedScheme

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

-- instance Core.MonadUnique m => Core.MonadUnique (InferM m) where
--   getUniqueSupplyM = InferM $ \_ stack fresh cs -> (stack, fresh, cs,) <$> Core.getUniqueSupplyM

instance Monad m => FromCore (InferM m) T where
  tycon d args = (\x -> Inj x d args) <$> fresh

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
    return (stack', fresh', cs `union` guardWith k x d cs', a)

-- Guard local constraints with one of several possible branches
-- branchAlts :: Monad m => [Guard] -> InferM m a -> InferM m a
-- branchAlts gs m = InferM $ \gamma stack fresh cs -> do 
--     (stack', fresh', cs', a) <- unInferM m gamma stack fresh cs
--     return (stack', fresh', cs' `union` guardAlts gs cs', a)

-- Extract a variable from the environment
getVar :: Monad m => Core.Var -> Core.Expr Core.Var -> InferM m (Scheme T)
getVar v e = getCtx >>= getVar'
  where
    getCtx :: Monad m => InferM m Context
    getCtx = InferM $ \gamma stack fresh cs -> return (stack, fresh, cs, gamma)

    getVar' :: Monad m => Context -> InferM m (Scheme T)
    getVar' gamma =
      case gamma M.!? Core.getName v of
        Just (RefinedScheme as xs cs u) -> do
          -- Localise constraints
          ys <- mapM (\x -> (x,) <$> fresh) xs
          emit $ foldr (uncurry rename) cs ys

          let u' = foldr (uncurry rename) u ys
          Forall as' v' <- fromCoreScheme $ Core.varType v

          -- TODO: Why don't these align!?
          -- when (as /= as') $ Core.pprPanic "Type variables don't align!" (Core.ppr (as, as'))
          let v'' = foldr (\(a, a') t -> subTyVar a' (Var a) t) v' (zip as as')
          emitSubType u' v'' e

          return $ Forall as' v'

        Nothing ->
          -- We can assume the variable is in scope as GHC hasn't emitted a warning
          -- Assume all externally defined terms are unrefined
         fromCoreScheme $ Core.varType v

-- Insert variables into the environment
putVar :: Core.Name -> RefinedScheme -> InferM m a -> InferM m a
putVar n t m = InferM $ \gamma -> unInferM m (M.insert n t gamma)

-- Insert many variables
putVars :: Context -> InferM m a -> InferM m a
putVars vs m = InferM $ \gamma -> unInferM m (M.union vs gamma)

-- Emit a constraint set to the environment
emit :: Monad m => ConSet -> InferM m ()
emit cs = InferM $ \gamma stack fresh cs' -> return (stack, fresh, cs `union` cs', ())

-- Emit a single constraint
emitSingle :: Monad m => K -> K -> Guard -> InferM m ()
emitSingle k1 k2 g = InferM $ \gamma stack fresh cs -> return (stack, fresh, insert k1 k2 g cs, ())

-- Convert a subtyping constraint to a constraint set and emit
emitSubType :: Monad m => Type T -> Type T -> Core.Expr Core.Var -> InferM m ()
emitSubType t1 t2 e
  | shape t1 /= shape t2                  = Core.pprPanic "Types must refine the same sort!" (Core.ppr (shape t1, shape t2, e))
emitSubType (t11 :=> t12) (t21 :=> t22) e = emitSubType t21 t11 e >> emitSubType t12 t22 e
emitSubType (Inj x d as) (Inj y _ as') e  -- TODO: Check tycon is saturated!
  | x /= y                                =  mapM_ (\(Core.getName -> n) -> emit (insert (Dom x n) (Dom y n) top empty)) (slice [d])
                                          >> mapM_ (\(a, a') -> emitSubType a a' e) (zip as as')
emitSubType _ _ _                         = return ()

-- Take the slice of a datatype
slice :: [Core.TyCon] -> [Core.TyCon]
slice tcs
  | tcs' == tcs = tcs
  | otherwise   = slice tcs'
  where
    tcs' = [tc' | tc <- tcs
                , dc <- Core.tyConDataCons tc
                , (Tcr.TyConApp tc' _) <- Core.dataConOrigArgTys dc
                , tc' `notElem` tcs
                , refinable tc']
                ++ tcs

-- Hide local constraints and attach them to variables
restrict :: Monad m => InferM m (M.Map Core.Name (Scheme T)) -> InferM m Context
restrict m = InferM $ \gamma stack fresh cs -> do
  (stack', fresh', cs', ts) <- unInferM m gamma stack fresh cs
  return (stack', fresh', cs, restrict' ts cs')
  where
    restrict' :: M.Map Core.Name (Scheme T) -> ConSet -> Context
    restrict' ts cs = fmap (\(Forall as t) -> RefinedScheme as xs cs' t) ts
      where
        xs  = L.nub (concatMap domain $ M.elems ts)
        cs' = saturate xs cs
