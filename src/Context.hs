{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, DeriveTraversable, DeriveFoldable, DeriveFunctor #-}

module Context where

import Types
import Expr
import Data.List hiding (insert, union)
import Data.Map.Strict as Map hiding (map, foldr)
import Control.Monad.Except
import Control.Monad.RWS hiding (Sum, Alt)
import Data.Functor.Const
import Debug.Trace

data ConGraph =
  ConGraph {
    succs :: Map Type [Type], -- Map (String, Bool, String) (Set Type)
    preds :: Map Type [Type],
    subs  :: Map (String, Bool, String) Type
  }
  | GVar String (Map String Type) (Map (String, Bool, String) Type)
  | Union ConGraph ConGraph
  deriving (Eq, Show)

data Context = Context {
    cst :: Map String Sort,
    con :: Map String (String, [Sort]), -- k -> (d, args)
    var :: Map String TypeScheme
} deriving Show

data TypeScheme = Forall [String] [(String, Bool, String)] ConGraph Type

instance Show TypeScheme where
  show (Forall as xs cs t) = "forall " ++ intercalate " " as ++ ". forall " ++ intercalate " " (map show xs) ++ "." ++ show cs ++ "=>" ++ show t

type Error = ErrorGen [Expr]

data ErrorGen a =
    TSError String Int Int a
  | CstError String a
  | ConError String a
  | VarError String a
  | DataTypeError String String a
  | ConstraintError Type Type a
  | CycleError [Type] a
  | EmptyCaseError a
  | CaseError a
  | AppError a
  | PatternError a
  | DoubleDefaultError a
  deriving (Functor, Foldable, Traversable)

instance Show Error where
  show (TSError x n m e) = "The variables " ++ show x ++" has " ++ show n ++ " type parameters but only " ++ show m ++" were applied." ++ inThe e
  show (CstError c e) = "The constant " ++ show c ++ " is not defined." ++ inThe e
  show (ConError k e) = "The constructor " ++ show k ++ " is not defined." ++ inThe e
  show (VarError v e) = "The variable " ++ show v ++ " is not defined." ++ inThe e
  show (DataTypeError d k e) = "The data type " ++ show d ++ " does not contain the constructor " ++ show k ++ inThe e
  show (ConstraintError t1 t2 e) = "The type " ++ show t1 ++ " does not refine " ++ show t2 ++ inThe e
  show (CycleError ts e) = "The refinement cycle " ++ show ts ++ " cannot be resolved." ++ inThe e
  show (EmptyCaseError e) = "Illegal empty case." ++ inThe e
  show (CaseError e) = "Case alternatives must have refine the same type." ++ inThe e
  show (AppError e) = "The expression is applied to too many arguments." ++ inThe e
  show (PatternError e) = "Pattern matching must asign all arguments to variables." ++ inThe e
  show (DoubleDefaultError e) = "Case cannot have multiple defaults." ++ inThe e

inThe :: [Expr] -> String
inThe = foldr (\e s -> (case e of {AltExpr a -> "\nIn the case alternative: "; otherwise -> "\nIn the expression: "}) ++ show e ++ s) "\n" . reverse

type InferM = RWST Context () Int (Except Error)

-- Bind expression to error
inExpr :: InferM a -> Expr -> InferM a
inExpr ma ex = ma `catchError` (throwError . (fmap (ex:)))

inAlt :: InferM a -> Alt -> InferM a
inAlt ma a = ma `inExpr` AltExpr a

-- inLet

safeCst :: String -> InferM Sort
safeCst s = do
  ctx <- ask
  case cst ctx !? s of
    Just t  -> return t
    Nothing -> throwError $ CstError s []

safeCon :: String -> InferM (String, [Sort])
safeCon k = do
  ctx <- ask
  case con ctx !? k of
    Just args -> return args
    Nothing   -> throwError $ ConError k []

safeVar :: String -> InferM (Maybe TypeScheme)
safeVar v = do
  ctx <- ask
  return $ var ctx !? v

insertVar :: String -> TypeScheme -> Context ->  Context
insertVar "$_sys$wild" _ ctx = ctx
insertVar "_" _ ctx = ctx
insertVar x f ctx = ctx{var = Map.insert x f $ var ctx}

insertMany :: [String] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (t:ts) ctx = insertVar x t (insertMany xs ts ctx)
insertMany _ _ _ = error "Pattern matching must include bind all constructor arguments"

delta :: Bool -> String -> String -> InferM [PType]
delta p d k = do
  ctx <- ask
  case con ctx !? k of
    Just (d', ts) -> if d == d'
      then return $ fmap (polarise p) ts
      else throwError $ DataTypeError d k []
    otherwise -> throwError $ ConError k []

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b) = PBase b
polarise p (SData d) = PData p d
polarise p (SArrow t1 t2) = PArrow (polarise (not p) t1) (polarise p t2)
