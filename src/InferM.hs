{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}

module InferM
    (
      InferM,
      Context (Context, con, var),
      safeVar,
      safeCon,
      fresh,
      freshScheme,
      insertVar,
      insertMany,
      throwInExpr
    ) where

import Errors
import Types
import Utils
import GenericConGraph
import Control.Monad.Except
import Control.Monad.RWS hiding (Sum)
import qualified Data.Map as M
import qualified GhcPlugins as Core
import UniqFM
import Debug.Trace

type InferM = RWST Context () Int (Except Error)

-- Extend a thrown exception
throwInExpr :: InferM a -> Core.Expr Core.Var -> InferM a
throwInExpr ma se = ma `catchError` (throwError . InExpr se)

-- Chagen to ghc maps
data Context = Context {
    con :: UniqFM {- Core.DataCon -} (Core.TyCon, [Sort]), -- k -> (d, args)
    var :: M.Map Core.Var TypeScheme
}

insertVar :: Core.Var -> TypeScheme -> Context ->  Context
insertVar x f ctx
  | isWild x  = ctx
  | otherwise = ctx{var = M.insert x f $ var ctx}

insertMany :: [Core.Var] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (t:ts) ctx = insertVar x t (insertMany xs ts ctx)

safeVar :: Core.Var -> InferM (TypeScheme)
safeVar v = do
  ctx <- ask
  case var ctx M.!? v of
    Just ts -> return ts
    Nothing -> throwError $ VariableError v

safeCon :: Core.DataCon -> InferM (Core.TyCon, [Sort])
safeCon k = do
  ctx <- ask
  case lookupUFM (con ctx) k of
    Just args -> return args
    Nothing   -> throwError $ ConstructorError k

fresh :: Sort -> InferM Type
fresh t = do
  i <- get
  put (i + 1)
  return $ head $ upArrow (show i) [polarise True t]

freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as (SVar a)) = return $ Forall as [] empty $ Con (TVar a) []
freshScheme (SForall as (SBase b)) = return $ Forall as [] empty $ Con (TBase b) []
freshScheme (SForall as s@(SData _)) = do
  t <- fresh s
  return $ Forall as [] empty t
freshScheme (SForall as (SArrow s1 s2)) = do
  Forall _ _ _ t1 <- freshScheme (SForall [] s1)  -- Fresh schemes have multiple refinement variables
  Forall _ _ _ t2 <- freshScheme (SForall [] s2)
  return $ Forall as [] empty (t1 :=> t2)

delta :: Bool -> Core.TyCon -> Core.DataCon -> InferM [PType]
delta p d k = do
  ctx <- ask
  case lookupUFM (con ctx) k of
    Just (d', ts) ->
      if d == d'
        then return $ fmap (polarise p) ts
        else throwError $ DataTypeError d k
    otherwise -> throwError $ ConstructorError k

instance Rewrite RVar UType InferM where
  toNorm t1@(K k ts) t2@(V x p d) = do
      args <- delta p d k
      let ts' = upArrow x args
      return [(K k ts', V x p d), (K k ts, K k ts')]
  toNorm t1@(V _ _ _) t2@(_ :=> _) = return [(t1, t2)]  -- Arrows are singleton sum so this shouldn't fall through
  toNorm t1@(V _ _ _) t2@(K _ _) = return [(t1, t2)]
  toNorm t1@(V x p d) t2@(Sum cs) = do
      s <- mapM refineCon cs
      return [(Sum s, Sum cs),(V x p d, Sum s)]
      where
        refineCon (TData k, ts) = do
          args <- delta p d k
          return (TData k, upArrow x args)
  toNorm t1 t2 = return [(t1, t2)]
