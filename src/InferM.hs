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
      TypeScheme (Forall),
      safeVar,
      safeCon,
      upArrow,
      fresh,
      polarise,
      fromCoreType,
      subTypeVars,
      Error (ConstraintError, ApplicationError, PolyTypeError)
    ) where

import GenericConGraph
import qualified Data.Map as M
import Control.Monad.RWS hiding (Sum)
import Control.Monad.Except
import qualified TyCoRep as T
import qualified GhcPlugins as Core

data Error = ConstraintError | ApplicationError | PolyTypeError

type InferM = RWST Context () Int (Except Error)

type ConGraph = ConGraphGen RVar UType
data Context = Context {
    con :: M.Map Core.Var (String, [Sort]), -- k -> (d, args)
    var :: M.Map Core.Var TypeScheme
}

type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] ConGraph Type

data RVar = RVar String Bool String deriving Eq

instance Ord RVar where
  RVar x _ _ <= RVar x' _ _ = x <= x'

data Sort = SVar Core.Var | SBase String | SData String | SArrow Sort Sort
data UType = TVar Core.Var | TBase String | TData String | TArrow | TCon Core.Var deriving Eq
data PType = PVar Core.Var | PBase String | PData Bool String | PArrow PType PType

instance Constructor UType where
  variance TArrow = [False, True]
  variance (TCon v) = repeat True
  variance _ = []

mkCon :: Core.Var -> [Type] -> SExpr RVar UType
mkCon v ts = Con (TCon v) ts

mkConArgs :: [Type] -> Type -> Type
mkConArgs ts y = foldr (\t1 t2 -> Con TArrow [t1, t2]) y ts

safeVar :: Core.Var -> InferM (TypeScheme)
safeVar v = do
  ctx <- ask
  case var ctx M.!? v of
    Just ts -> return ts
    Nothing -> error "Variable not in environment."

safeCon :: Core.Var -> InferM (String, [Sort])
safeCon k = do
  ctx <- ask
  case con ctx M.!? k of
    Just args -> return args
    Nothing   -> error "Cosntructor not in environment."

fromCoreType :: Core.Type -> Sort
fromCoreType (T.TyVarTy v) = SVar v
fromCoreType (T.FunTy t1 t2) = SArrow (fromCoreType t1) (fromCoreType t2)
fromCoreType _ = error "Unimplemented"

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
subTypeVars (a:as) (t:ts) (TVar a')
  | a == a' = subTypeVars as ts t
  | otherwise = TVar a'
subTypeVars (a:as) (t:ts) t' = subTypeVars as ts t'
