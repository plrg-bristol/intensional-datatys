{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, TypeSynonymInstances #-}

module InferM
    (
      InferM,
      safeVar,
      safeCon,
      fresh,
      freshScheme,
      insertVar,
      insertMany
    ) where

import Errors
import Types
import Utils
import GenericConGraph
import Control.Monad.Except
import Control.Monad.RWS hiding (Sum)
import qualified Data.Map as M

type InferM = RWST Context () Int (Except Error)

data Context = Context {
    con :: M.Map Var (Var, [Sort]), -- k -> (d, args)
    var :: M.Map Var TypeScheme
}

insertVar :: Var -> TypeScheme -> Context ->  Context
insertVar x f ctx
  | isWild x  = ctx
  | otherwise = ctx{var = M.insert x f $ var ctx}

insertMany :: [Var] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (t:ts) ctx = insertVar x t (insertMany xs ts ctx)

safeVar :: Var -> InferM (TypeScheme)
safeVar v = do
  ctx <- ask
  case var ctx M.!? v of
    Just ts -> return ts
    Nothing -> error "Variable not in environment."

safeCon :: Var -> InferM (Var, [Sort])
safeCon k = do
  ctx <- ask
  case con ctx M.!? k of
    Just args -> return args
    Nothing   -> error "Constructor not in environment."

fresh :: Sort -> InferM Type
fresh t = do
    i <- get
    put (i + 1)
    return $ head $ upArrow (show i) [polarise True t]

freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as s) = do
  t <- fresh s
  return $ Forall as [] empty t

delta :: Bool -> Var -> Var -> InferM [PType]
delta p d k = do
  ctx <- ask
  case con ctx M.!? k of
    Just (d', ts) -> if d == d'
      then return $ fmap (polarise p) ts
      else throwError DataTypeError
    otherwise -> throwError ConstructorError

instance Rewrite RVar UType InferM where
  toNorm t1@(K k ts) t2@(V x p d) = do
      args <- delta p d k
      let ts' = upArrow x args
      if ts' /= ts
        then return [(K k ts', V x p d), (K k ts, K k ts')]
        else return [(t1, t2)]
  toNorm t1@(V x p d) t2@(Sum cs) = do
      s <- mapM (refineCon x d) cs
      if cs /= s
        then return [(Sum s, Sum cs),(V x p d, Sum s)]
        else return [(t1, t2)]
      where
        refineCon :: String -> Var -> (UType, [Type]) -> InferM (UType, [Type])
        refineCon x d (TCon k, ts) = do
          args <- delta p d k
          return (TCon k, upArrow x args)
