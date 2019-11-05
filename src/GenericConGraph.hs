{-# LANGUAGE PatternSynonyms, MultiParamTypeClasses, FlexibleInstances #-}

module GenericConGraph (
      SExpr (Var, Con, Sum, One, Zero, Dot)
    , Constructor (variance)
    , ConGraphGen (ConGraph, succs, preds, subs)
    , Rewrite (toNorm)
    , empty
    , fromList
    , toList
    , purge
    , saturate
    , insert
    , union
    , substitute
    , graphMap
    -- , leastSolution
     ) where

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Trans.Maybe
import qualified Data.Map as M
import qualified Data.List as L
import Data.Bifunctor (second)
import Debug.Trace

-- Set expression with disjoint sum
data SExpr x c = Var x | Sum [(c, [SExpr x c])] | One | Dot

-- Singleton sum
pattern Con :: c -> [SExpr x c] -> SExpr x c
pattern Con c args = Sum [(c, args)]

-- Empty sum
pattern Zero :: SExpr x c
pattern Zero = Sum []

instance (Eq c, Eq x) => Eq (SExpr x c) where
  Var x == Var y    = x == y
  Sum cs == Sum ds  = (length cs == length ds) && all (uncurry (==)) (zip cs ds)
  One == One        = True
  _ == _            = False

-- Constructors are named and explicitly co- or contra- variant in arguments
class Constructor c where
  variance  :: c -> [Bool]

-- Constraint graph
data ConGraphGen x c = ConGraph {
  succs :: M.Map x [SExpr x c],
  preds :: M.Map x [SExpr x c],
  subs  :: M.Map x (SExpr x c)    -- Unique representations for cyclic equivalence classes
}

-- Empty constraint graph
empty :: ConGraphGen x c
empty = ConGraph { succs = M.empty, preds = M.empty, subs = M.empty }

-- Additional deterministic rewriting rules for constriants
class Rewrite x c m where
  toNorm :: SExpr x c -> SExpr x c -> m [(SExpr x c, SExpr x c)]

instance (Monad m, Rewrite x c m) => Rewrite x c (MaybeT m) where
  -- toNorm :: SExpr x c -> SExpr x c -> MaybeT m [(SExpr x c, SExpr x c)]
  toNorm se1 se2 = MaybeT (Just <$> toNorm se1 se2)

-- Constructor a new constraint graph from a list
fromList :: (Rewrite x c m, Monad m, Ord x, Constructor c, Eq c) => [(SExpr x c, SExpr x c)] -> MaybeT m (ConGraphGen x c)
fromList = foldM (\cg (t1, t2) -> insert t1 t2 cg) empty

-- Returns a list of constraints as internally represented
toList :: ConGraphGen x c -> [(SExpr x c, SExpr x c)]
toList ConGraph{succs = s, preds = p} = [(Var k, v) |(k, vs) <- M.toList s, v <- vs] ++ [(v, Var k) |(k, vs) <- M.toList p, v <- vs]

-- Eagerly remove properly scoped intermediate nodes
purge :: (Ord x, Constructor c, Eq c) => (x -> Bool) -> ConGraphGen x c -> ConGraphGen x c
purge p' cg = foldr remove cg $ filter (\n -> all (\(n1, n2) -> notElem n [n1, n2] || (p n1 && p n2)) edges) $ filter p nodes
  where
    p n = case n of {Var v -> p' v; _ -> False}
    nodes = concat [[n1, n2] | (n1, n2) <- toList cg]
    edges = toList cg
    remove n ConGraph{succs = s, preds = p, subs = sb} = ConGraph{succs = mapRemove n s, preds = mapRemove n p, subs = sb}

-- Remove a nodes from the graph
mapRemove :: (Eq x, Eq c) => SExpr x c -> M.Map x [SExpr x c] -> M.Map x [SExpr x c]
mapRemove n m = M.filterWithKey (\k _ -> Var k /= n) $ fmap (filter (/= n)) m

-- Does an element occur uniquely in the list
isUnique :: Eq a => a -> [a] -> Bool
isUnique a xs = case go Nothing a xs of {Just x -> x; Nothing -> False}
    where go s _ [] = s
          go s@Nothing x (z:zs)
            | x == z = go (Just True) x zs
            | otherwise = go s x zs
          go s@(Just True) x (z:zs)
            | x == z = Just False
            | otherwise = go s x zs
          go s@(Just False) _ _ = s

-- The fixed point of normalisation and transitivity
saturate :: (Eq c, Eq x, Monad m, Rewrite x c m) => ConGraphGen x c -> m [(SExpr x c, SExpr x c)]
saturate = saturate' . toList
  where
    saturate' cs = do
      delta <- concatMapM (\(a, b) -> concatMapM (\(b', c) -> if b == b' then toNorm a c else return []) cs) cs
      let cs' = L.nub (cs ++ delta)
      if cs == cs'
        then return cs
        else saturate' cs'

    concatMapM op = foldr f (return [])
      where
        f x xs = do x <- op x; if null x then xs else do xs <- xs; return $ x++xs

-- Apply function to set expressions without effecting variables
graphMap :: (Eq c, Ord x, Constructor c) => (SExpr x c -> SExpr x c) -> ConGraphGen x c -> ConGraphGen x c
graphMap f cg@ConGraph{succs = s, preds = p, subs = sb} =
  ConGraph {
    succs = fmap (fmap f) s,
    preds = fmap (fmap f) p,
    subs = fmap f sb
  }

-- Insert new constraint with rewriting rule
insert :: (Rewrite x c m, Monad m, Ord x, Constructor c, Eq c) => SExpr x c -> SExpr x c -> ConGraphGen x c -> MaybeT m (ConGraphGen x c)
insert t1 t2 cg = do
  cs <- toNorm t1 t2
  foldM (\cg (t1', t2') -> insertInner t1' t2' cg) cg cs

-- Insert new constraint
insertInner :: (Rewrite x c m, Monad m, Ord x, Constructor c, Eq c) => SExpr x c -> SExpr x c -> ConGraphGen x c -> MaybeT m (ConGraphGen x c)
insertInner Dot _ cg = return cg
insertInner _ Dot cg = return cg -- Ignore any constriants concerning Dot
insertInner x y cg
  | x == y                          = return cg
insertInner _ One cg                = return cg
insertInner Zero _ cg               = return cg
insertInner One t cg                = mzero
insertInner t Zero cg               = mzero
insertInner vx@(Var x) vy@(Var y) cg
  | x > y                           = insertSucc x vy cg
  | otherwise                       = insertPred vx y cg
insertInner cx@(Con c cargs) dy@(Con d dargs) cg
  | c == d                          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else  insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                       = mzero
insertInner (Var x) c@(Sum _) cg    = insertSucc x c cg
insertInner c@(Con _ _) (Var y) cg  = insertPred c y cg
insertInner cx@(Con c cargs) (Sum ((d, dargs):ds)) cg
  | c == d                          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                       = insert cx (Sum ds) cg
insertInner (Sum cs) t cg           = foldM (\cg (c, cargs) -> insert (Con c cargs) t cg) cg cs

insertSucc :: (Rewrite x c m, Monad m, Eq c, Ord x, Constructor c) => x -> SExpr x c -> ConGraphGen x c -> MaybeT m (ConGraphGen x c)
insertSucc x sy cg@ConGraph{succs = s, subs = sb} =
  case sb M.!? x of
    Just z    -> insert z sy cg
    _ ->
      case s M.!? x of
        Just ss ->
          if sy `elem` ss
            then return cg
            else do
              cg' <- closeSucc x sy cg{succs = M.insert x (sy:ss) s}
              case predChain cg' x sy [] of
                Just vs -> foldM (substitute sy) cg' vs
                _ -> return cg'
        _ -> closeSucc x sy cg{succs = M.insert x [sy] s}

insertPred:: (Rewrite x c m, Monad m, Eq c, Ord x, Constructor c) => SExpr x c -> x -> ConGraphGen x c -> MaybeT m (ConGraphGen x c)
insertPred sx y cg@ConGraph{preds = p, subs = sb} =
  case sb M.!? y of
    Just z    -> insert sx z cg
    _ ->
      case p M.!? y of
        Just ps ->
          if sx `elem` ps
            then return cg
            else do
              cg' <- closePred sx y cg{preds = M.insert y (sx:ps) p}
              case succChain cg' sx y [] of
                Just vs -> foldM (substitute sx) cg' vs
                _ -> return cg'
        _ -> closePred sx y cg{preds = M.insert y [sx] p}

-- Partial online transitive closure
closeSucc :: (Rewrite x c m, Monad m, Eq c, Ord x, Constructor c) => x -> SExpr x c -> ConGraphGen x c -> MaybeT m (ConGraphGen x c)
closeSucc x sy cg =
  case preds cg M.!? x of
    Just ps   -> foldM (\cg p -> insert p sy cg) cg ps
    _ -> return cg

closePred :: (Rewrite x c m, Monad m, Eq c, Ord x, Constructor c) => SExpr x c -> x -> ConGraphGen x c -> MaybeT m (ConGraphGen x c)
closePred sx y cg =
  case succs cg M.!? y of
    Just ss   -> foldM (flip $ insert sx) cg ss
    _ -> return cg

-- Partial online cycle elimination
predChain :: (Eq c, Ord x, Constructor c) => ConGraphGen x c -> x -> SExpr x c -> [x] -> Maybe [x]
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

succChain :: (Eq c, Ord x, Constructor c) => ConGraphGen x c -> SExpr x c -> x -> [x] -> Maybe [x]
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

-- Union of constraint graphs
union :: (Rewrite x c m, Monad m, Eq c, Ord x, Constructor c) => ConGraphGen x c -> ConGraphGen x c -> MaybeT m (ConGraphGen x c)
union cg1@ConGraph{subs = sb} cg2@ConGraph{succs = s, preds = p, subs = sb'} = do
  -- Combine equivalence classes using left representation
  let msb  = M.union sb $ fmap subVar sb'

  -- Update cg1 with new equivalences
  cg1' <- M.foldrWithKey (\x se -> (>>= \cg -> substitute se cg x)) (return cg1) msb

  -- Insert edges from cg2 into cg1
  cg1'' <- M.foldrWithKey (\k vs -> (>>= \cg -> foldM (flip (insert (Var k))) cg vs)) (return cg1') s
  M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert v (Var k) cg') cg vs)) (return cg1'') p
  where
    subVar (Var x) = M.findWithDefault (Var x) x sb
    subVar (Sum cs) = Sum $ fmap (second (fmap subVar)) cs
    suBVar One = One

-- Safely substitute variable (x) with expression (se)
substitute :: (Rewrite x c m, Monad m, Eq c, Ord x, Constructor c) => SExpr x c -> ConGraphGen x c -> x -> MaybeT m (ConGraphGen x c)
substitute se ConGraph{succs = s, preds = p, subs = sb} x = do
  -- Necessary to recalculate preds and succs as se might not be a Var.
  -- If se is a Var this insures there are no redundant edges (i.e. x < x) or further simplifications.
  cg' <- case p' M.!? x of
    Just ps -> foldM (\cg pi -> insert pi se cg) cg ps
    Nothing -> return cg
  cg'' <- case s' M.!? x of
    Just ss -> foldM (flip $ insert se) cg' ss
    Nothing -> return cg'
  return cg''{ succs = M.delete x $ succs cg'', preds = M.delete x $ preds cg''}
  where
    sub (Var y) | x == y = se
    sub (Sum cs) = Sum $ fmap (second (fmap sub)) cs
    sub t = t
    p'  = fmap (L.nub . fmap sub) p
    s'  = fmap (L.nub . fmap sub) s
    cg = ConGraph { succs = s', preds = p', subs = M.insert x se $ fmap sub sb }
