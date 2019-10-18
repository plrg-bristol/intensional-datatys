{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, DeriveTraversable, DeriveFoldable, DeriveFunctor #-}

module Context
  (
    Context,
    ConGraph,
    Type,
    UType,
    RVar,
    InferM
  ) where

-- import Types
import Expr
import GenericConGraph
import Data.List hiding (insert, union)
import Data.Map.Strict as Map hiding (map, foldr)
import Control.Monad.Except
import Control.Monad.RWS hiding (Sum, Alt)
import Data.Functor.Const
import Debug.Trace

data Context = Context {
    cst :: Map String Sort,
    con :: Map String (String, [Sort]), -- k -> (d, args)
    var :: Map String TypeScheme
}

type ConGraph = ConGraphGen RVar UType
type Type = SExpr RVar UType

data UType = TVar String | TBase String | TData String| Type :=> Type deriving Eq
data RVar = RVar String Bool String deriving (Show, Eq)

-- Polarised type
data PType = PVar String | PBase String | PData Bool String | PArrow PType PType deriving (Show, Ord, Eq)

data Sort = SVar String | SBase String | SData String | SArrow Sort Sort

instance Show Sort where
  show (SVar v) = v
  show (SBase b) = b
  show (SData d) = d
  show (SArrow t1 t2) = "(" ++ show t1 ++ "->" ++ show t2 ++ ")"

data SortScheme = SForall [String] Sort

-- instance Show SortScheme where
--   show (SForall as s) = "forall " ++ intercalate " " as ++ "." ++ show s

instance Show UType where
  show (TVar v) = v
  show (TBase b) = b
  show (TData d) = d
  show (t1 :=> t2) = "(" ++ show t1 ++ "->" ++ show t2 ++ ")"

instance Ord RVar where
  (RVar x p d) >= (RVar x' p' d') = x >= x'

data TypeScheme = Forall [String] [(String, Bool, String)] ConGraph Type

upArrow :: String -> [PType] -> [Type]
upArrow x = map upArrow'
  where
    upArrow' (PData p d)     = RVar x p d
    upArrow' (PArrow t1 t2)  = upArrow' t1 :=> upArrow' t2
    upArrow' (PVar a)        = TVar a
    upArrow' (PBase b)       = TBase b

-- instance Show TypeScheme where
--   show (Forall as xs cs t) = "forall " ++ intercalate " " as ++ ". forall " ++ intercalate " " (map show xs) ++ "." ++ show cs ++ "=>" ++ show t

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

newInt :: InferM Int
newInt = do
    i <- get
    put (i + 1)
    return i

fresh :: Sort -> InferM Type
fresh t = do
    i <- newInt
    return $ head $ upArrow (show i) [polarise True t]

-- freshScheme :: SortScheme -> InferM TypeScheme
-- freshScheme (SForall as s) = do
--     i <- newInt
--     j <- newInt
--     return $ Forall as [] (GVar (show j) Map.empty Map.empty) $ head $ upArrow (show i) [polarise True s]

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
