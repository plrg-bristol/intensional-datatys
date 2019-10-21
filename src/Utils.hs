{-# LANGUAGE PatternSynonyms, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module Utils
    (
      Sort (SVar, SBase, SData, SArrow),
      UType (TArrow, TData),
      RVar (RVar),
      -- empty,
      -- insert,
      stems,
      -- substitute,
      sub,
      SExpr (K, (:=>)),
      Type,
      ConGraph,
      InferM,
      isConstructor,
      fromPolyVar,
      insertMany,
      TypeScheme (Forall),
      safeVar,
      safeCon,
      -- upArrow,
      fresh,
      -- polarise,
      toSort,
      insertVar,
      subTypeVars,
      toFreshTypeScheme,
      Error (ConstraintError, ApplicationError, PolyTypeError)
    ) where

import GenericConGraph
import qualified Data.Map as M
import Control.Monad.RWS hiding (Sum)
import Control.Monad.Except
import qualified TyCoRep as T
import qualified DataCon as D
import qualified GhcPlugins as Core

data Error = ConstraintError | ApplicationError | PolyTypeError | ConstructorError | DataTypeError

type InferM = RWST Context () Int (Except Error)

type ConGraph = ConGraphGen RVar UType
data Context = Context {
    con :: M.Map Core.Var (Core.Var, [Sort]), -- k -> (d, args)
    var :: M.Map Core.Var TypeScheme
}

type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] ConGraph Type

newtype RVar = RVar (String, Bool, Core.Var) deriving Eq

instance Ord RVar where
  RVar (x, _, _) <= RVar (x', _, _) = x <= x'

data Sort = SVar Core.Var | SBase String | SData Core.Var | SArrow Sort Sort
data UType = TVar Core.Var | TBase String | TData D.DataCon | TArrow | TCon Core.Var deriving Eq
data PType = PVar Core.Var | PBase String | PData Bool Core.Var | PArrow PType PType

instance Constructor UType where
  variance TArrow = [False, True]
  variance (TCon v) = repeat True
  variance _ = []

instance ConstraintError RVar UType Error where
  usingEquivalence = undefined
  fromCycle = undefined
  fromClosure = undefined
  hetrogeneousConstructors = undefined
  subtypeOfZero = undefined
  supertypeOfOne = undefined

insertVar :: Core.Var -> TypeScheme -> Context ->  Context
insertVar x f ctx
  | (Core.nameStableString $ Core.getName x) == "$_sys$wild" = ctx
  | otherwise                                                = ctx{var = M.insert x f $ var ctx}

insertMany :: [Core.Var] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (t:ts) ctx = insertVar x t (insertMany xs ts ctx)

pattern (:=>) :: Type -> Type -> Type
pattern t1 :=> t2 = Con TArrow [t1, t2]

pattern K :: Core.Var -> [Type] -> Type
pattern K v ts = Con (TCon v) ts

pattern V :: String -> Bool -> Core.Var -> Type
pattern V x p d = Var (RVar (x, p, d))

safeVar :: Core.Var -> InferM (TypeScheme)
safeVar v = do
  ctx <- ask
  case var ctx M.!? v of
    Just ts -> return ts
    Nothing -> error "Variable not in environment."

safeCon :: Core.Var -> InferM (Core.Var, [Sort])
safeCon k = do
  ctx <- ask
  case con ctx M.!? k of
    Just args -> return args
    Nothing   -> error "Constructor not in environment."

toSort :: Core.Type -> Sort
toSort (T.TyVarTy v) = SVar v
toSort (T.FunTy t1 t2) = SArrow (toSort t1) (toSort t2)
toSort _ = error "Core type is not a sort."

toFreshTypeScheme :: Core.Type -> InferM TypeScheme
toFreshTypeScheme (T.TyVarTy v) = do
  t <- fresh (SVar v)
  return $ Forall [] [] empty t
toFreshTypeScheme (T.FunTy t1 t2) = do
  ft1 <- fresh (toSort t1)
  ft2 <- fresh (toSort t2)
  return $ Forall [] [] empty (ft1 :=> ft2)
toFreshTypeScheme (T.ForAllTy b t) = do
  (Forall as xs cg ft) <- toFreshTypeScheme t
  let a = Core.binderVar b
  return $ Forall (a:as) xs cg ft
toFreshTypeScheme _ = error "Unimplemented."

fresh :: Sort -> InferM Type
fresh t = do
    i <- get
    put (i + 1)
    return $ head $ upArrow (show i) [polarise True t]

upArrow :: String -> [PType] -> [Type]
upArrow x = fmap upArrow'
  where
    upArrow' (PData p d)     = Var $ RVar (x, p, d)
    upArrow' (PArrow t1 t2)  = Con TArrow [upArrow' t1, upArrow' t1]
    upArrow' (PVar a)        = Con (TVar a) []
    upArrow' (PBase b)       = Con (TBase b) []

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b) = PBase b
polarise p (SData d) = PData p d
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)

sub :: [RVar] -> [Type] -> Type -> Type
sub _ _ Zero = Zero
sub _ _ One = One
sub [] _ t = t
sub _ [] t = t
sub (x:xs) (y:ys) (Var x')
  | x == x' = y
  | otherwise = sub xs ys (Var x')
sub xs ys (Con c cargs) = Con c $ fmap (sub xs ys) cargs
sub xs ys (Sum cs) = Sum $ fmap (\(c, cargs) -> (c, fmap (sub xs ys) cargs)) cs

subTypeVars :: [Core.Var] -> [Type] -> Type -> Type
subTypeVars [] _ u = u
subTypeVars _ [] u = u
subTypeVars (a:as) (t:ts) (Con (TVar a') [])
  | a == a' = subTypeVars as ts t
  | otherwise = subTypeVars as ts $ Con (TVar a') []
subTypeVars (a:as) (t:ts) (Sum [(TVar a', [])])
  | a == a' = subTypeVars as ts t
  | otherwise = subTypeVars as ts $ Con (TVar a') []
subTypeVars (a:as) (t:ts) t' = subTypeVars as ts t'

isConstructor :: Core.Id -> Bool
isConstructor = undefined

fromPolyVar :: Core.CoreExpr -> Maybe (Core.Id, [Sort])
fromPolyVar (Core.Var i) = Just (i, [])
fromPolyVar (Core.App e1 (Core.Type t)) = do
  (id, ts) <- fromPolyVar e1
  return (id, toSort t:ts)
fromPolyVar _ = Nothing

stems :: Type -> [String]
stems (Var (RVar (x, _, _))) = [x]
stems (Con c cargs) = concatMap stems cargs
stems (Sum cs) = concatMap (\(_, cargs) -> concatMap stems cargs) cs
stems _ = []

delta :: Bool -> Core.Var -> Core.Var -> InferM [PType]
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
        refineCon :: String -> Core.Var -> (UType, [Type]) -> InferM (UType, [Type])
        refineCon x d (TCon k, ts) = do
          args <- delta p d k
          return (TCon k, upArrow x args)
