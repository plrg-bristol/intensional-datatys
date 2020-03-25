{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}

module Scheme (
  Scheme(..),
  pattern Mono,
  pattern Forall,
  mono,
  applyType,
) where

import Prelude hiding ((<>))
import qualified Data.Set as S

import Types

import Name
import Binary
import Outputable

-- Constrained polymorphic types
data Scheme (e :: Extended) d c = Scheme {
  tyvars      :: [Name],
  boundvs     :: S.Set Int,
  body        :: Type e d,
  constraints :: c
}

instance (Refined (Type e d), Refined c) => Refined (Scheme e d c) where
  freevs s = (freevs (body s) `S.union` freevs (constraints s)) S.\\ boundvs s

  rename x y s
    | x `elem` boundvs s = s
    | y `elem` boundvs s = pprPanic "unimplemented" $ ppr (x, y)
    | otherwise = Scheme {
        tyvars      = tyvars s,
        boundvs     = boundvs s,
        body        = rename x y $ body s,
        constraints = rename x y $ constraints s
      }

instance (Outputable c, Outputable d, Refined c) => Outputable (Scheme e d c) where
  ppr Scheme{ tyvars = as , boundvs = q, body = t, constraints = c } =
    hang (pprTyVars <> pprConVars <> ppr t)
       2 (hang (text "where") 2 (ppr c))
    where
      pprTyVars
        | null as   = empty
        | otherwise = forAllLit <+> fsep (map ppr as) <> dot
      pprConVars
        | null q    = empty
        | otherwise = forAllLit <+> fsep (ppr <$> S.toList q) <> dot

instance (Binary (Type e d), Binary c) => Binary (Scheme e d c) where
  put_ bh Scheme { tyvars = as, boundvs = q, body = t, constraints = cs } = do
    put_ bh as
    put_ bh $ S.toList q
    put_ bh cs
    put_ bh t

  get bh = do
    as <- get bh
    q  <- get bh
    cs <- get bh
    t  <- get bh
    return $ Scheme { tyvars = as, boundvs = S.fromList q, body = t, constraints = cs }

pattern Mono :: Type e d -> Scheme e d ()
pattern Mono t = Scheme {
  tyvars      = [],
  body        = t,
  constraints = ()
}

pattern Forall :: [Name] -> Type e d -> Scheme e d ()
pattern Forall as t = Scheme {
  tyvars      = as,
  body        = t,
  constraints = ()
}

-- Demand a monomorphic type
mono :: Outputable d => Scheme T d () -> Type T d
mono (Mono t) = t
mono s        = pprPanic "Higher rank types are unimplemented!" $ ppr s

-- Type application
applyType :: Outputable d => Scheme e d () -> Type e d -> Scheme e d ()
applyType (Forall (a:as) u)   t = Forall as $ subTyVar a t u
applyType (Mono Ambiguous)    _ = Mono Ambiguous
applyType (Mono (Base b as))  t = Mono $ Base b (as ++ [shape t])
applyType (Mono (Data d as))  t = Mono $ Data d (as ++ [t])
applyType (Mono (Inj x d as)) t = Mono $ Inj x d (as ++ [t])
applyType (Mono (Var a))      t = Mono $ App (Var a) (shape t)
applyType (Mono (App a b))    t = Mono $ App (App a b) (shape t)
applyType t t'                  = pprPanic "The type is saturated!" $ ppr (t, t')

-- Type variable substitution
subTyVar :: Outputable d => Name -> Type e d -> Type e d -> Type e d
subTyVar a t (Var a')
  | a == a'    = t
  | otherwise  = Var a'
subTyVar a t (App x y) =
  case body $ applyType (Mono $ subTyVar a (shape t) x) $ subTyVar a (shape t) y of
    Base b as -> Base b as
    Var a     -> Var a
    App a b   -> App a b
    _         -> pprPanic "Invalid application in types!" $ ppr (x, y)
subTyVar a t (x :=> y)    = subTyVar a t x :=> subTyVar a t y
subTyVar a t (Base b as)  = Base b (subTyVar a (shape t) <$> as)
subTyVar a t (Data d as)  = Data d (subTyVar a t <$> as)
subTyVar a t (Inj x d as) = Inj x d (subTyVar a t <$> as)
subTyVar _ _ t            = t
