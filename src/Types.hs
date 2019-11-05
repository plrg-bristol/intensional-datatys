{-# LANGUAGE PatternSynonyms, FlexibleInstances #-}

module Types
    (
      Sort (SVar, SArrow, SData, SBase),
      SortScheme (SForall),
      UType (TVar, TData, TArrow, TBase, TLit),
      PType,
      RVar (RVar),
      Type,
      TypeScheme (Forall),
      SExpr (V, K, B, (:=>)),
      ConGraph,
      upArrow,
      polarise,
      subTypeVars,
      subSortVars,
      sub,
      stems,
      toSort,
      toSortScheme,
      fromPolyVar,
      isPrim,
      disp
    ) where

import Prelude hiding ((<>))
import Data.List
import GenericConGraph
import qualified GhcPlugins as Core
import Debug.Trace
import Data.Bifunctor (second)
import qualified TyCoRep as T
import qualified Data.Map as M
import Control.Monad.RWS hiding (Sum, Alt, (<>))
import Outputable

newtype RVar = RVar (Int, Bool, Core.TyCon, [Sort]) deriving Eq

instance Ord RVar where
  RVar (x, _, _, _) <= RVar (x', _, _, _) = x <= x'

data Sort = SVar Core.Var | SBase Core.TyCon [Sort] | SData Core.TyCon [Sort] | SArrow Sort Sort {- | SApp Sort Sort | SConApp Core.TyCon [Sort] -} deriving Show
data UType = 
    TVar Core.Var 
  | TBase Core.TyCon [Sort]
  | TData Core.DataCon [Sort]
  | TArrow 
  | TLit Core.Literal -- Sums can contain literals

  {-  
  | TApp Sort Sort    -- Unrefinable & externally defined
  | TConApp Core.TyCon [Sort] -- Buggy pattern matching 
  -}

data PType = PVar Core.Var | PBase Core.TyCon [Sort] | PData Bool Core.TyCon [Sort] | PArrow PType PType {- | PApp Sort Sort | PConApp Core.TyCon [Sort] -}
type Type = SExpr RVar UType
data TypeScheme = Forall [Core.Var] [RVar] [(Type, Type)] Type
data SortScheme = SForall [Core.Var] Sort deriving Show

isPrim :: Core.NamedThing t => t -> Bool
isPrim t = isPrefixOf "$ghc-prim$" $ name t

isConstructor :: Core.Var -> Maybe Core.DataCon
isConstructor = Core.isDataConId_maybe

name :: Core.NamedThing a => a -> String
name = Core.nameStableString . Core.getName

fromPolyVar :: Core.CoreExpr -> Maybe (Core.Var, [Sort])
fromPolyVar (Core.Var i) = Just (i, [])
fromPolyVar (Core.App e1 (Core.Type t)) = do
  (i, ts) <- fromPolyVar e1
  return (i, ts ++ [toSort t])
fromPolyVar _ = Nothing

toSort :: Core.Type -> Sort
toSort (T.TyVarTy v) = SVar v
toSort (T.FunTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SArrow s1 s2
toSort (T.TyConApp t args) 
  -- | isPrim t = SBase t $ fmap toSort args
  | otherwise = SData t $ fmap toSort args

toSort (T.AppTy t1 t2) = error "Unimplemented" -- From external (unrefined modules)
  -- let s1 = toSort t1
  --     s2 = toSort t2
  -- in SApp s1 s2

toSort _ =  error "Core type is not a valid sort." -- Lit, cast and coercion

toSortScheme :: Core.Type -> SortScheme
toSortScheme (T.TyVarTy v) = SForall [] (SVar v)
toSortScheme (T.FunTy t1 t2) =
  let s1 = toSort t1
      s2 = toSort t2
  in SForall [] (SArrow s1 s2)
toSortScheme (T.ForAllTy b t) =
  let (SForall as st) = toSortScheme t
      a = Core.binderVar b
  in SForall (a:as) st
toSortScheme (T.TyConApp t args)
  -- | isPrim t = SForall [] $ SBase t $ fmap toSort args
  | otherwise = SForall [] $ SData t $ fmap toSort args
toSortScheme _ = error "Core type is not a valid sort scheme."

instance Core.Outputable UType where
  ppr (TVar v) = ppr v
  ppr (TBase b ss) = ppr b <> intercalate' "@" (fmap ppr ss)
  ppr (TData dc ss) = ppr dc <> intercalate' "@" (fmap ppr ss)

instance Show UType where
  show (TVar v) = show v
  show (TBase b ss) = show b ++ intercalate "@" (fmap show ss)
  show (TData dc ss) = show dc ++ intercalate "@" (fmap show ss)

instance Core.Outputable RVar where
  ppr (RVar (x, p, d, ss)) = text "[" <> ppr x <> (if p then text"+" else text "-") <> ppr d <> intercalate' "@" (fmap ppr ss) <> text "]"

instance Show RVar where
  show (RVar (x, p, d, ss)) = "[" ++ show x ++ (if p then "+" else "-") ++ show d ++ intercalate "@" (fmap show ss) ++ "]"

intercalate' :: String -> [SDoc] -> SDoc
intercalate' s [] = text ""
intercalate' s [d] = text (" " ++ s) <> d
intercalate' s (d:ds) = d <> text s <> intercalate' s ds

instance Core.Outputable Type where
  ppr (V x p d ss) = text "[" <> ppr x <> (if p then text "+" else text "-") <> ppr d <> intercalate' "@" (fmap ppr ss) <>  text "]"
  ppr (t1 :=> t2) =  text "(" <> ppr t1 <>  text "->" <> (ppr t2) <>  text ")"
  ppr (K v ss ts) = ppr v <> intercalate' "@" (fmap ppr ss) <> text "(" <> interpp'SP ts <>  text ")"
  ppr (Sum cs) = pprWithBars (\(c, cargs) -> ppr c <>  text "(" <> interpp'SP cargs <> text ")") cs

instance Core.Outputable Sort where
  ppr (SVar a) = ppr a
  ppr (SBase d ss) = ppr d <> intercalate' "@" (fmap ppr ss)
  ppr (SData d ss) = ppr d <> intercalate' "@" (fmap ppr ss)
  ppr (SArrow s1 s2) = ppr s1 <> text "->" <> ppr s2

instance Show Type where
  show (V x p d ss) = "[" ++ show x ++ (if p then "+" else "-") ++ show d ++ intercalate "@" (fmap show ss) ++ "]"
  show (t1 :=> t2) =  "(" ++ show t1 ++  "->" ++ show t2 ++  ")"
  show (K v ss ts) = show v ++ intercalate "@" (fmap show ss) ++ "(" ++ intercalate "," (fmap show ts) ++ ")"
  show (Sum cs) = intercalate " | " (fmap (\(c, cargs) -> show c ++ "(" ++ intercalate "," (fmap show cargs) ++ ")") cs)

-- instance Core.Outputable TypeScheme where
--   ppr (Forall as xs cg t) = text "∀" <> interppSP as <> text ".∀"  <> interppSP xs <> text "." <> ppr t <> text "where:" <> interppSP (toList cg)

disp as xs cs t = "∀" ++ intercalate ", " (fmap show as) ++ ".∀" ++ intercalate ", " (fmap show xs) ++ "." ++ show t ++ "\nwhere:\n" ++ intercalate ";\n" (fmap f cs)
  where
    f (t1, t2) = show t1 ++ " < " ++ show t2

instance Eq UType where
  TVar x == TVar y = Core.getName x == Core.getName y
  TBase b ss == TBase b' ss' = Core.getName b == Core.getName b' && ss == ss'
  TData d args == TData d' args' = Core.getName d == Core.getName d' && args == args'
  TLit l == TLit l' = l == l'
  TArrow == TArrow = True
  _ == _ = False

instance Eq Sort where
  SVar x == SVar y = Core.getName x == Core.getName y
  SBase b ss == SBase b' ss' = Core.getName b == Core.getName b' && ss == ss'
  SData d args == SData d' args' = Core.getName d == Core.getName d' && args == args'
  SArrow s1 s2 == SArrow s1' s2' = s1 == s1' && s2 == s2'
  _ == _ = False

type ConGraph = ConGraphGen RVar UType

instance Core.Outputable ConGraph where
  ppr ConGraph{succs = s, preds = p, subs =sb} = ppr s <> text "\n" <> ppr p <> text "\n" <> (text $ show sb)

split :: String -> [String]
split [] = [""]
split (c:cs) | c == '$'  = "" : rest
             | otherwise = (c : head rest) : tail rest
    where rest = split cs

-- assume everything is coming from the same module
instance Show Core.Var where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Show Core.Name where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Show Core.TyCon where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Show Core.DataCon where
  show n = last $ split (Core.nameStableString $ Core.getName n)

instance Constructor UType where
  variance TArrow = [False, True]
  variance _ = repeat True

pattern (:=>) :: Type -> Type -> Type
pattern t1 :=> t2 = Con TArrow [t1, t2]

pattern K :: Core.DataCon -> [Sort] -> [Type] -> Type
pattern K v ss ts = Con (TData v ss) ts

pattern V :: Int -> Bool -> Core.TyCon -> [Sort] -> Type
pattern V x p d ss = Var (RVar (x, p, d, ss))

pattern B :: Core.TyCon -> [Sort] -> Type
pattern B b args = Con (TBase b args) []

stems :: Type -> [Int]
stems (V x _ _ _) = [x]
stems (Sum cs) = concatMap (\(_, cargs) -> concatMap stems cargs) cs
stems _ = []

upArrow :: Int -> [PType] -> [Type]
upArrow x = fmap upArrow'
  where
    upArrow' (PData p d args) = Var $ RVar (x, p, d, args)
    upArrow' (PArrow t1 t2)  = upArrow' t1 :=> upArrow' t2
    upArrow' (PVar a)        = Con (TVar a) []
    upArrow' (PBase b ss)        = Con (TBase b ss) []

polarise :: Bool -> Sort -> PType
polarise p (SVar a) = PVar a
polarise p (SBase b ss) = PBase b ss
polarise p (SData d args) = PData p d args
polarise p (SArrow s1 s2) = PArrow (polarise (not p) s1) (polarise p s2)

-- Find a better way to perform these substituions a "type" typeclass
sub :: [RVar] -> [Type] -> Type -> Type
sub [] [] t = t
sub (x:xs) (y:ys) (Var x')
  | x == x' = y
  | otherwise = sub xs ys (Var x')
sub xs ys (Sum cs) = Sum $ fmap (second $ fmap (sub xs ys)) cs
sub _ _ _ = error "Substitution vectors have different lengths"

subSortVars :: [Core.Var] -> [Sort] -> Sort -> Sort
subSortVars [] [] u = u
subSortVars (a:as) (t:ts) (SVar a')
  | a == a' = t
  | otherwise = subSortVars as ts $ SVar a'
subSortVars as ts (SBase b ss) = SBase b $ fmap (subSortVars as ts) ss
subSortVars as ts (SData d ss) = SData d $ fmap (subSortVars as ts) ss
subSortVars as ts (SArrow s1 s2) = SArrow (subSortVars as ts s1) (subSortVars as ts s2)

-- If the type is a lifted sort return the sort, otherwise fail i.e. has the type undergone some refinement
broaden :: Type -> Sort
broaden (V x p d ss) = SData d ss
broaden (Con (TVar a) []) = SVar a
broaden (B b ss) =  SBase b ss
broaden (t1 :=> t2) = SArrow (broaden t1) (broaden t2)
broaden (K v ss ts) = error "" -- Constructors only as refinements of data types
broaden (Con (TLit _) _) = error "" -- TLit only occurs as a result of case analysis

subTypeVars :: [Core.Var] -> [Type] -> Type -> Type
subTypeVars [] [] u = u
subTypeVars (a:as) (t:ts) (Con (TVar a') [])
  | a == a' = t
  | otherwise = subTypeVars as ts $ Con (TVar a') []
subTypeVars as ts (B b ss) = 
  let ts'' = fmap broaden ts
  in B b $ (fmap (subSortVars as ts'') ss)
subTypeVars as ts (K v ss ts') =
  let ts'' = fmap broaden ts
  in K v (fmap (subSortVars as ts'') ss) (fmap (subTypeVars as ts) ts')
subTypeVars as ts (V x p d ss) = 
  let ts'' = fmap broaden ts
  in V x p d (fmap (subSortVars as ts'') ss)
subTypeVars as ts (t1 :=> t2) = subTypeVars as ts t1 :=> subTypeVars as ts t2
subTypeVars as ts  l@(Con (TLit _) []) = l
subTypeVars as ts (Sum cs) = Sum $ fmap (\(c, args) -> (c, fmap (subTypeVars as ts) args)) cs

-- subTypeVars as ts (Con (TApp s1 s2) []) = 
--   let ss = map broaden ts 
--   in Con (TApp (subSortVars as ss s1) (subSortVars as ss s2)) []
-- subTypeVars as ts (Con (TConApp tc args) []) = 
--   let ss = map broaden ts
--   in Con (TConApp tc (subSortVars as ss <$> args)) []
