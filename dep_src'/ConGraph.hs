{-# LANGUAGE MultiParamTypeClasses, BangPatterns #-}

module ConGraph (
      ConGraph (ConGraph, succs, preds)
    , empty
    , fromList
    , toList
    , guardWith

    , insert
    , substituteMany
    , union
     ) where

import Control.Applicative hiding (empty)
import Control.Monad.RWS hiding (Sum)

import Data.Maybe
import Data.Bifunctor
import qualified Data.Map as M
import qualified Data.List as L

import qualified GhcPlugins as Core

import Types
import InferM
import PrettyPrint

-- Constraint graph
data ConGraph = ConGraph {
  succs :: M.Map RVar [(Guard, Type)],
  preds :: M.Map RVar [(Guard, Type)]
}

-- Empty constraint graph
empty :: ConGraph
empty = ConGraph { succs = M.empty, preds = M.empty }

-- Constructor a new constraint graph from a list
fromList :: [(Guard, Type, Type)] -> Core.Expr Core.Var -> ConGraph
fromList cs e = foldr (\(g, t1, t2) cg -> insert g t1 t2 cg e) empty cs

-- Returns a list of constraints as internally represented (incomplete)
toList :: ConGraph -> [(Guard, Type, Type)]
toList ConGraph{succs = s, preds = p} = [(g, Var k, v) | (k, vs) <- M.toList s, (g, v) <- vs] ++ [(g, v, Var k) | (k, vs) <- M.toList p, (g, v) <- vs]

-- Add the guard to all constriants
guardWith :: Core.Name -> Type -> ConGraph -> ConGraph
guardWith n (Var r) cg@ConGraph{succs = s, preds = p} = let g = [(n, r)] in cg{succs = M.map (fmap $ first (++ g)) s, preds = M.map (fmap $ first (++ g)) p}
guardWith n (Sum _ _ _ cs) cg | n `elem` [k | (Data k _ _, _) <- cs] = cg
                              | otherwise = empty

instance TypeVars ConGraph Type where
  {-# SPECIALIZE instance TypeVars ConGraph Type #-}
  subTypeVar v t cg@ConGraph{succs = s, preds = p} =
    ConGraph {
      succs = M.mapKeys varMap $ subTypeVar v t s,
      preds = M.mapKeys varMap $ subTypeVar v t p
    }
    where
      varMap (RVar (x, d, as)) = RVar (x, d, subTypeVar v t <$> as)




      
-- Normalise the constraints by applying recursive simplifications
normalise :: Guard -> Type -> Type -> [(Guard, Type, Type)]
normalise _ t1 t2
  | t1 == t2 = []
normalise g (t11 :=> t12) (t21 :=> t22) = normalise g t21 t11 ++ normalise g t12 t22
normalise g (Con o d k as ts) (Sum o' d' as' ((k', ts'):ss))
  | k == k' && as == as' = concat $ zipWith (normalise g) ts ts'
  | otherwise = normalise g (Con o d k as ts) (Sum o' d' as' ss)
normalise g t1@(Con o d k as ts) t2@(V x d' as') =
  let ts' = upArrowDataCon x k as
  in (g, Con o d k as ts', V x d' as') : normalise g (Con o d k as ts) (Con o d k as ts')
normalise g t1@(V x d as) t2@(Sum o d' as' cs) =
  let cs' = map (\(k, ts) -> (k, upArrowDataCon x k as')) cs
  in (g, V x d as, Sum o d' as' cs') : concatMap (\(d'@(Data k _ _), ts) -> concat $ zipWith (normalise ((k, RVar (x, d, as)) : g)) ts (upArrowDataCon x d' as')) cs
normalise g t1 t2 = [(g, t1, t2)]

-- Insert new constraint with normalisation
insert :: Guard -> Type -> Type -> ConGraph -> Core.Expr Core.Var -> ConGraph
insert g t1 t2 _ e | incomparable t1 t2 = 
  Core.pprPanic "Sorts must algin" (Core.ppr (t1, t2, e)) undefined

insert g t1@(Sum e1 tc as cs) t2@(Sum e2 tc' as' ds) cg e | any (`notElem` fmap fst ds) $ fmap fst cs = 
  Core.pprPanic "Invalid sum!" (Core.ppr (t1, t2, e1, e2, e, toList cg))

insert g t1 t2 cg _ = foldr (\(g', t1', t2') -> insertInner g' t1' t2') cg $ normalise g t1 t2

-- Insert new constraint
insertInner :: Guard -> Type -> Type -> ConGraph -> ConGraph
insertInner g vx@(Var x) vy@(Var y) cg
  | x > y                        = insertSucc g x vy cg
  | otherwise                    = insertPred g vx y cg
insertInner g (Var x) c@Sum{} cg = insertSucc g x c cg
insertInner g c@Con{} (Var y) cg = insertPred g c y cg

insertSucc :: Guard -> RVar -> Type -> ConGraph -> ConGraph
insertSucc g x sy cg@ConGraph{succs = s} =
  case s M.!? x of
    Just ss ->
      if (g, sy) `elem` ss
        then cg
        else cg{succs = M.insert x ((g, sy):ss) s}
    _ -> cg{succs = M.insert x [(g, sy)] s}

insertPred :: Guard -> Type -> RVar -> ConGraph -> ConGraph
insertPred g sx y cg@ConGraph{preds = p} =
  case p M.!? y of
    Just ps ->
      if (g, sx) `elem` ps
        then cg
        else cg{preds = M.insert y ((g, sx):ps) p}
    _ -> cg{preds = M.insert y [(g, sx)] p}

-- Substitute many variables
substituteMany :: [RVar] -> [Type] -> ConGraph -> Core.Expr Core.Var -> ConGraph
substituteMany _ [] cg _ = cg
substituteMany (r:rs) (t:ts) cg@ConGraph{succs = s, preds = p} e =
  -- Necessary to recalculate preds and succs as se might not be a Var.
  -- If se is a Var this insures there are no redundant edges (i.e. x < x) or further simplifications anyway
  let cg' = cg{ succs = M.map (fmap $ second $ subRefinementVar r t) $ M.delete r s,
                preds = M.map (fmap $ second $ subRefinementVar r t) $ M.delete r p}

      cg'' = case p M.!? r of
        Just ps -> foldr (\(g, pi) cg -> insert g (subRefinementVar r t pi) t cg e) cg' ps
        Nothing -> cg'

      cg''' = case s M.!? r of
        Just ss -> foldr (\(g, si) cg -> insert g t (subRefinementVar r t si) cg e) cg'' ss
        Nothing -> cg''
  
  in substituteMany rs ts cg''' e

-- Union of constraint graphs
union :: ConGraph -> ConGraph -> Core.Expr Core.Var -> ConGraph
union cg1 cg2@ConGraph{succs = s, preds = p} e =
  -- Insert edges from cg2 into cg1
  let cg1' = M.foldrWithKey (\k vs cg -> foldr (\(g, v) cg' -> insert g (Var k) v cg' e) cg vs) cg1 s
  in M.foldrWithKey (\k vs cg -> foldr (\(g, v) cg' -> insert g v (Var k) cg' e) cg vs) cg1' p