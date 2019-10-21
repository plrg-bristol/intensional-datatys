{-# LANGUAGE PatternSynonyms, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module InferM
    (
      Sort (SVar, SBase, SData, SArrow),
      UType (TArrow),
      mkCon,
      mkConArgs,
      RVar (RVar),
      empty,
      insert,
      substitute,
      sub,
      Type,
      ConGraph,
      InferM,
      insertMany,
      TypeScheme (Forall),
      safeVar,
      safeCon,
      upArrow,
      fresh,
      polarise,
      toSort,
      mkArrow,
      desugarArrow,
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
import qualified GhcPlugins as Core

data Error = ConstraintError | ApplicationError | PolyTypeError | ConstructorError

type InferM = RWST Context () Int (Except Error)

type ConGraph = ConGraphGen RVar UType
data Context = Context {
    con :: M.Map Core.Var (Core.Var, [Sort]), -- k -> (d, args)
    var :: M.Map Core.Var TypeScheme
}

type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] ConGraph Type

data RVar = RVar String Bool Core.Var deriving Eq

instance Ord RVar where
  RVar x _ _ <= RVar x' _ _ = x <= x'

data Sort = SVar Core.Var | SBase String | SData Core.Var | SArrow Sort Sort
data UType = TVar Core.Var | TBase String | TData Core.Var | TArrow | TCon Core.Var deriving Eq
data PType = PVar Core.Var | PBase String | PData Bool Core.Var | PArrow PType PType

instance Constructor UType where
  variance TArrow = [False, True]
  variance (TCon v) = repeat True
  variance _ = []

insertVar :: Core.Var -> TypeScheme -> Context ->  Context
insertVar x f ctx
  | (Core.nameStableString $ Core.getName x) == "$_sys$wild" = ctx
  | otherwise                                                = ctx{var = M.insert x f $ var ctx}

insertMany :: [Core.Var] -> [TypeScheme] -> Context -> Context
insertMany [] [] ctx = ctx
insertMany (x:xs) (t:ts) ctx = insertVar x t (insertMany xs ts ctx)

mkCon :: Core.Var -> [Type] -> SExpr RVar UType
mkCon v ts = Con (TCon v) ts

mkArrow :: Type -> Type -> Type
mkArrow t1 t2 = Con TArrow [t1, t2]

mkConArgs :: [Type] -> Type -> Type
mkConArgs ts y = foldr (\t1 t2 -> Con TArrow [t1, t2]) y ts

desugarArrow :: Type -> (Type, Type)
desugarArrow (Sum [(TArrow, [t3, t4])]) = (t3, t4)
desugarArrow (Con TArrow [t3, t4]) = (t3, t4)
desugarArrow _ = error "Type isn't an arrow"

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
  return $ Forall [] [] empty (mkArrow ft1 ft2)
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
    upArrow' (PData p d)     = Var $ RVar x p d
    upArrow' (PArrow t1 t2)  = Con TArrow [upArrow' t1, upArrow' t1]
    upArrow' (PVar a)        = Con (TVar a) []
    upArrow' (PBase b)       = Con (TBase b) []

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b) = PBase b
polarise p (SData d) = PData p d
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)

sub :: M.Map RVar Type -> Type -> Type
sub m (Var x) = case m M.!? x of
  Just t -> t
  otherwise -> Var x
sub m Zero = Zero
sub m One = One
sub m (Con c cargs) = Con c $ fmap (sub m) cargs
sub m (Sum cs) = Sum $ fmap (\(c, cargs) -> (c, fmap (sub m) cargs)) cs

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

insert' :: Type -> Type -> ConGraph -> InferM ConGraph
insert' t@(Con (TCon c) cargs) (Var (RVar x p d)) cg = do
  (d, args) <- safeCon c
  let t' = upArrow x $ fmap (polarise p) args
  if d /= c
    then throwError ConstructorError
    else
      case do
        cg' <- insert t (Con (TCon c) t') cg
        insert (Con (TCon c) t') (Var (RVar x p d)) cg'
      of
        Just cg'  -> return cg'
        otherwise -> throwError ConstraintError
-- insert' r@(Var (RVar x p d)) t@(Sum cs) cg = do
--   (d, args) <- safeCon c
--   let t' = upArrow x $ fmap (polarise p) args
--   if d /= c
--     then throwError ConstructorError
--     else
--       case do
--         cg' <- insert t (Con (TCon c) t') cg
--         insert (Con (TCon c) t') (Var (RVar x p d)) cg'
--       of
--         Just cg'  -> return cg'
--         otherwise -> throwError ConstraintError
-- insert' t1 t2 cg = insert t1 t2 cg
