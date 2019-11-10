{-# LANGUAGE MultiParamTypeClasses, BangPatterns #-}

module ConGraph (
      ConGraph (ConGraph, succs, preds, subs)
    , empty
    , fromList
    , toList

    , insert
    , substitute
    , union

    , closeScope
    , saturate
     ) where

import Control.Applicative hiding (empty)
import Control.Monad.RWS hiding (Sum)

import Data.Bifunctor (second)
import qualified Data.Map as M
import qualified Data.List as L

import qualified GhcPlugins as Core

import Types
import InferM
import PrettyPrint

-- Constraint graph
data ConGraph = ConGraph {
  succs :: M.Map RVar [Type],
  preds :: M.Map RVar [Type],
  subs  :: M.Map RVar Type        -- Unique representations for cyclic equivalence classes
}

-- Empty constraint graph
empty :: ConGraph
empty = ConGraph { succs = M.empty, preds = M.empty, subs = M.empty }

-- Constructor a new constraint graph from a list
fromList :: [(Type, Type)] -> Core.Expr Core.Var -> InferM ConGraph
fromList ts e = foldM (\cg (t1, t2) -> insert t1 t2 cg e) empty ts

-- Returns a list of constraints as internally represented (incomplete)
toList :: ConGraph -> [(Type, Type)]
toList ConGraph{succs = s, preds = p} = [(Var k, v) | (k, vs) <- M.toList s, v <- vs] ++ [(v, Var k) | (k, vs) <- M.toList p, v <- vs]

instance TypeVars ConGraph Type where
  {-# SPECIALIZE instance TypeVars ConGraph Type #-}
  subTypeVar v t cg@ConGraph{succs = s, preds = p, subs = sb} =
    ConGraph {
      succs = M.mapKeys varMap $ fmap (subTypeVar v t) <$> s,
      preds = M.mapKeys varMap $ fmap (subTypeVar v t) <$> p,
      subs  = M.mapKeys varMap (subTypeVar v t <$> sb)
    }
    where
      varMap (RVar (x, p, d, as)) = RVar (x, p, d, subTypeVar v t <$> as)





-- Normalise the constraints by applying recursive simplifications
toNorm :: Type -> Type -> InferM [(Type, Type)]
toNorm t1@(Con e k as ts) t2@(V x p d as') = do
  args <- delta p d k as
  let ts' = upArrow x <$> args
  if ts' /= ts
    then do
      c1 <- toNorm (Con e k as ts') (V x p d as')
      c2 <- toNorm (Con e k as ts) (Con e k as ts')
      return (c1 ++ c2)
    else return [(Con e k as ts', V x p d as'), (Con e k as ts, Con e k as ts')]

toNorm t1@(V x p d as) t2@(Sum e cs) = do
  cs' <- mapM refineCon cs
  if cs' /= cs
    then do
      c1 <- toNorm (Sum e cs') (Sum e cs)
      c2 <- toNorm (V x p d as) (Sum e cs')
      return (c1 ++ c2)
    else return [(Sum e cs', Sum e cs), (V x p d as, Sum e cs)]
  where
    refineCon (k, as, ts) = do
      args <- delta p d k as
      return (k, as, upArrow x <$> args)

toNorm t1 t2 = return [(t1, t2)]

-- Insert new constraint with normalisation
insert :: Type -> Type -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
insert t1 t2 cg e = do
  cs <- toNorm t1 t2
  foldM (\cg (t1', t2') -> insertInner t1' t2' cg e) cg cs

-- Insert new constraint
insertInner :: Type -> Type -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
insertInner Dot _ cg _ = return cg
insertInner _ Dot cg _ = return cg -- Ignore any constriants concerning Dot

insertInner x y cg _ | x == y = return cg

insertInner (t1 :=> t2) (t1' :=> t2') cg e = do
  cg' <- insert t1' t1 cg e
  insert t2 t2' cg' e

insertInner t1@(Sum e1 cs) t2@(Sum e2 ds) _ e
  | any (`notElem` cons ds) $ cons cs = Core.pprPanic "Invalid sum!" (Core.ppr (t1, e1, t2, e2, e))

insertInner cx@(Con _ c as cargs) dy@(Con _ d as' dargs) cg e
  | c == d && as == as'          = foldM (\cg (ci, di) -> insert ci di cg e) cg $ zip cargs dargs

insertInner cx@(Con _ c as cargs) (Sum e1 ((d, as', dargs):ds)) cg e
  | c == d && as == as'          = foldM (\cg (ci, di) -> insert ci di cg e) cg $ zip cargs dargs
  | otherwise                    = insert cx (Sum e1 ds) cg e

insertInner vx@(Var x) vy@(Var y) cg e
  | x > y                        = insertSucc x vy cg e
  | otherwise                    = insertPred vx y cg e

insertInner (Var x) c@(Sum _ _) cg e = insertSucc x c cg e
insertInner c@Con{} (Var y) cg e     = insertPred c y cg e

insertInner (Sum e cs) t cg _ = foldM (\cg (c, as, cargs) -> insert (Con e c as cargs) t cg e) cg cs

insertInner t1 t2 cg _ = Core.pprPanic "Error!" (Core.ppr (t1, t2)) -- This should be unreachable

insertSucc :: RVar -> Type -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
insertSucc x sy cg@ConGraph{succs = s, subs = sb} e =
  case sb M.!? x of
    Just z    -> insert z sy cg e
    _ ->
      case s M.!? x of
        Just ss ->
          if sy `elem` ss
            then return cg
            else do
              cg' <- closeSucc x sy cg{succs = M.insert x (sy:ss) s} e
              -- TODO: intersect sums
              case predChain cg' x sy [] of
                Just vs -> foldM (\cg x -> substitute x sy cg e) cg' vs
                _ -> return cg'
        _ -> closeSucc x sy cg{succs = M.insert x [sy] s} e

insertPred :: Type -> RVar -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
insertPred sx y cg@ConGraph{preds = p, subs = sb} e =
  case sb M.!? y of
    Just z    -> insert sx z cg e
    _ ->
      case p M.!? y of
        Just ps ->
          if sx `elem` ps
            then return cg
            else do
              cg' <- closePred sx y cg{preds = M.insert y (sx:ps) p} e
              -- TODO: union sums
              case succChain cg' sx y [] of
                Just vs -> foldM (\cg y -> substitute y sx cg e) cg' vs
                _ -> return cg'
        _ -> closePred sx y cg{preds = M.insert y [sx] p} e

-- Partial online transitive closure
closeSucc :: RVar -> Type -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
closeSucc x sy cg e =
  case preds cg M.!? x of
    Just ps   -> foldM (\cg p -> insert p sy cg e) cg ps
    _ -> return cg

closePred :: Type -> RVar -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
closePred sx y cg e =
  case succs cg M.!? y of
    Just ss   -> foldM (\cg p -> insert sx p cg e) cg ss
    _ -> return cg

-- Partial online cycle elimination
predChain :: ConGraph -> RVar -> Type -> [RVar] -> Maybe [RVar]
predChain cg f (Var t) m = do
  guard $ f == t
  return $ f:m
predChain cg f t m = do
  ps <- preds cg M.!? f
  foldr (\t pl -> predLoop t <|> pl) Nothing ps
  where
    m' = f:m
    predLoop (Var p) = do
      guard $ p `elem` m' || p > f
      predChain cg p t m'
    predLoop t' = do
      guard $ t == t'
      return m'

succChain :: ConGraph -> Type -> RVar -> [RVar] -> Maybe [RVar]
succChain cg (Var f) t m = do
  guard $ f == t
  return $ t:m
succChain cg f t m = do
  ss <- succs cg M.!? t
  foldr (\f sl -> succLoop f <|> sl) Nothing ss
  where
    m' = t:m
    succLoop (Var s) = do
      guard $ s `elem` m' || t <= s
      succChain cg f s m'
    succLoop f' = do
      guard $ f == f'
      return m'

-- Safely substitute variable with an expression
substitute :: RVar -> Type -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
substitute x se ConGraph{succs = s, preds = p, subs = sb} e = do
  -- Necessary to recalculate preds and succs as se might not be a Var.
  -- If se is a Var this insures there are no redundant edges (i.e. x < x) or further simplifications anyway
  cg' <- case p' M.!? x of
    Just ps -> foldM (\cg pi -> insert pi se cg e) cg ps
    Nothing -> return cg
  cg'' <- case s' M.!? x of
    Just ss -> foldM (\cg pi -> insert se pi cg e) cg' ss
    Nothing -> return cg'
  return cg''{ succs = M.delete x $ succs cg'', preds = M.delete x $ preds cg''}
  where
    p'  = fmap (fmap $ subRefinementVar x se) p
    s'  = fmap (fmap $ subRefinementVar x se) s
    cg = ConGraph { succs = s', preds = p', subs = M.insert x se (subRefinementVar x se <$> sb) }

-- Union of constraint graphs
union :: ConGraph -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
union cg1@ConGraph{subs = sb} cg2@ConGraph{succs = s, preds = p, subs = sb'} e = do
  -- Combine equivalence classes using left representation
  let msb  = M.union sb (subRefinementMap sb <$> sb')

  -- Update cg1 with new equivalences
  cg1' <- M.foldrWithKey (\x se -> (>>= \cg -> substitute x se cg e)) (return cg1) msb

  -- Insert edges from cg2 into cg1
  cg1'' <- M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert (Var k) v cg' e) cg vs)) (return cg1') s
  M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert v (Var k) cg' e) cg vs)) (return cg1'') p





-- Eagerly remove properly scoped bounded (intermediate) nodes that are not associated with the environment's stems (optimisation)
closeScope :: Int -> ConGraph -> Core.Expr Core.Var -> InferM ConGraph
{-# INLINE closeScope #-}
closeScope scope cg@ConGraph{subs = sb} e = do
  ctx <- ask
  let varTypes = M.elems $ var ctx
  let envStems = concatMap (\(Forall _ ns cs t) -> [j | RVar (j, _, _, _) <- ns] ++ concat (concat [[stems c1, stems c2] | (c1, c2) <- cs]) ++ stems t) varTypes
  
  -- Filter irrelevant variable, i.e. those that have gone out of scope and cannot be accessed by the environment
  let p v = case v of {(V x _ _ _) ->  x <= scope || (x `elem` envStems); _ -> True}

  cs <- saturate cg
  fromListWith $ [(n1, n2) | (n1, n2) <- cs, p n1 || p n2]
  where
    fromListWith = foldM (\cg (t1, t2) -> insert t1 t2 cg e) ConGraph{succs = M.empty, preds = M.empty, subs = sb}

-- The fixed point of normalisation and transitivity
saturate :: ConGraph -> InferM [(Type, Type)]
{-# INLINE saturate #-}
saturate cg@ConGraph{subs = sb} = saturate' $ toList cg
  where
    saturate' cs = do
      -- Normalise all transitive edges in cs
      delta <- concatMapM (\(a, b) -> concatMapM (\(b', c) -> if b == b' then toNorm a c else return []) cs) cs
      let delta' = [(subRefinementMap sb d1, subRefinementMap sb d2) | (d1, d2) <- delta]

      -- Add new edges
      let cs' = L.nub (cs ++ delta')

      -- Until a fixed point is reached
      if cs == cs'
        then return cs
        else saturate' cs'
    
    concatMapM op = foldr go $ return []
      where
        go x xs = do x <- op x; if null x then xs else do xs <- xs; return $ x++xs