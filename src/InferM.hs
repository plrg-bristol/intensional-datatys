{-# LANGUAGE MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances #-}

module InferM
    (
      Sort (SVar, SBase, SData, (:=>)),
      UType (TArrow),
      mkCon,
      mkConType,
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
      sortFromCoreType
    ) where

import GenericConGraph
import qualified Data.Map as M
import Control.Monad.RWS hiding (Sum)
import Control.Monad.Except
import qualified TyCoRep as T
import qualified GhcPlugins as Core

data Error = Error
type InferM = RWST Context () Int (Except Error)

type ConGraph = ConGraphGen UType RVar
data Context = Context {
    con :: M.Map Core.Var (String, [Sort]), -- k -> (d, args)
    var :: M.Map Core.Var TypeScheme
}

type Type = SExpr UType RVar
data TypeScheme = Forall [String] [RVar] ConGraph Type

data RVar = RVar String Bool String deriving Eq

instance Ord RVar where
  RVar x _ _ <= RVar x' _ _ = x <= x'

infixr :=>
data Sort = SVar Core.Var | SBase String | SData String | Sort :=> Sort
data UType x = TVar Core.Var | TBase String | TData String | TArrow Type Type | TCon Core.Var [Type]
data PType = PVar Core.Var | PBase String | PData Bool String | PArrow PType PType

instance Constructor UType RVar where
  name (TVar v) = "$v"
  name (TBase b) = "$b"
  name (TData d) = d
  name (TCon s _) = Core.nameStableString $ Core.getName s
  name (TArrow _ _) = "->"

  variance (TArrow _ _) = [False, True]
  variance (TCon _ as) = replicate (length as) True
  variance _ = []

  args (TArrow t1 t2) = [t1, t2]
  args (TCon _ a) = a
  args _ = []

mkCon :: Core.Var -> [Type] -> SExpr UType RVar
mkCon v ts = Con $ TCon v ts

mkConType :: [Type] -> Type -> Type
mkConType ts y = foldr (\t1 t2 -> Con $ TArrow t1 t2) y ts

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

sortFromCoreType :: Core.Type -> Sort
sortFromCoreType (T.TyVarTy v) = SVar v
sortFromCoreType (T.FunTy t1 t2) = sortFromCoreType t1 :=> sortFromCoreType t2
sortFromCoreType _ = error "Unimplemented"

fresh :: Sort -> InferM Type
fresh t = do
    i <- get
    put (i + 1)
    return $ head $ upArrow (show i) [polarise True t]

upArrow :: String -> [PType] -> [Type]
upArrow x = fmap upArrow'
  where
    upArrow' (PData p d)     = Var $ RVar x p d
    upArrow' (PArrow t1 t2)  = Con (TArrow (upArrow' t1) (upArrow' t1))
    upArrow' (PVar a)        = Con (TVar a)
    upArrow' (PBase b)       = Con (TBase b)

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b) = PBase b
polarise p (SData d) = PData p d
polarise p (t1 :=> t2) = PArrow (polarise (not p) t1) (polarise p t2)

sub :: M.Map RVar Type -> Type -> Type
sub m (Var x) = case m M.!? x of
  Just t -> t
  otherwise -> Var x
sub m Zero = Zero
sub m One = One
sub m (Con c) = Con $ sub' m c
sub m (Sum cs) = Sum $ fmap (sub' m) cs

sub' :: M.Map RVar Type -> UType RVar -> UType RVar
sub' m (TArrow t1 t2) = TArrow (sub m t1) (sub m t2)
sub' m t = t
