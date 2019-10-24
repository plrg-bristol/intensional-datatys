{-# LANGUAGE PatternSynonyms, MultiParamTypeClasses, FunctionalDependencies #-}

module GenericConGraph (
      SExpr (Var, Con, Sum, One, Zero)
    , Constructor (variance)
    , ConGraphGen (ConGraph, succs, preds)
    , ConstraintError (usingEquivalence, fromCycle, fromClosure, hetrogeneousConstructors, subtypeOfZero, supertypeOfOne)
    , Rewrite (toNorm)
    , empty
    , fromList
    , nodes
    , path
    , insert
    , union
    , substitute
    , graphMap
     ) where

import Control.Applicative hiding (empty)
import Control.Monad
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.List as L
import Debug.Trace

-- Set expression with disjoint sum
data SExpr x c = Var x | Sum [(c, [SExpr x c])] | One deriving Show

-- Singleton sum
pattern Con :: c -> [SExpr x c] -> SExpr x c
pattern Con c args = Sum [(c, args)]

-- Empty sum
pattern Zero :: SExpr x c
pattern Zero = Sum []

instance (Eq c, Eq x) => Eq (SExpr x c) where
  Var x == Var y    = x == y
  Sum cs == Sum ds  = (length cs == length ds) && (all (uncurry (==)) $ zip cs ds)
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
} deriving Show

-- Empty constraint graph
empty :: ConGraphGen x c
empty = ConGraph { succs = M.empty, preds = M.empty, subs = M.empty }

-- Extend an existing MonadError with constraint specific errors
class ConstraintError x c e | c -> x where
  -- Contextual error information
  usingEquivalence          :: x -> SExpr x c -> e -> e
  fromCycle                 :: [x] -> SExpr x c -> e -> e
  fromClosure               :: SExpr x c -> SExpr x c -> e -> e

  -- Base errors
  hetrogeneousConstructors  :: SExpr x c -> SExpr x c -> e
  subtypeOfZero             :: SExpr x c -> e
  supertypeOfOne            :: SExpr x c -> e

-- Extend a thrown exception
throwContext :: MonadError e m => m a -> (e -> e) -> m a
throwContext ma f = ma `catchError` (throwError . f)

-- Additional deterministic rewriting rules for constriants
class Rewrite x c m where
  toNorm :: SExpr x c -> SExpr x c -> m [(SExpr x c, SExpr x c)]

-- Constructor a new constraint graph from a list
fromList :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Ord x, Constructor c, Eq c) => [(SExpr x c, SExpr x c)] -> m (ConGraphGen x c)
fromList = foldM (\cg (t1, t2) -> insert t1 t2 cg) empty

-- A list of all nodes that appear in the constriant graph
nodes :: ConGraphGen x c -> [SExpr x c]
nodes ConGraph{succs = s, preds = p} = fmap Var (M.keys s) ++ fmap Var (M.keys p) ++ concat (M.elems s ++ M.elems p)

-- This needs to be iterative deepening
path :: (Eq c, Show c, Show x, Ord x) => ConGraphGen x c -> [SExpr x c] -> [SExpr x c] -> SExpr x c -> Bool
path cg@ConGraph{succs = s, preds = p} visited [] _ = False
path cg@ConGraph{succs = s, preds = p} visited (x:xs) z
  | x == z = True
  | elem x visited = path cg visited xs z
  | otherwise = path cg (x:visited) (expand x xs) z
  where
    expand x xs = L.nub (edges x ++ (fmap Var $ M.keys $ M.map (filter (== x)) p) ++ xs)
    edges (Var x) = case s M.!? x of
      Just ss -> ss
      otherwise -> []
    edges _ = []

-- Insert new constraint with rewriting rule
insert :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Ord x, Constructor c, Eq c) => SExpr x c -> SExpr x c -> ConGraphGen x c -> m (ConGraphGen x c)
insert t1 t2 cg = do
  cs <- toNorm t1 t2
  foldM (\cg (t1', t2') -> insertInner t1' t2' cg) cg cs

-- Insert new constraint
insertInner :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Ord x, Constructor c, Eq c) => SExpr x c -> SExpr x c -> ConGraphGen x c -> m (ConGraphGen x c)
insertInner x y cg
  | x == y                          = return cg
insertInner _ One cg                = return cg
insertInner Zero _ cg               = return cg
insertInner One t cg                = throwError $ supertypeOfOne t
insertInner t Zero cg               = throwError $ subtypeOfZero t
insertInner vx@(Var x) vy@(Var y) cg
  | x > y                           = insertSucc x vy cg
  | otherwise                       = insertPred vx y cg
insertInner cx@(Con c cargs) dy@(Con d dargs) cg
  | c == d                          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                       = throwError $ hetrogeneousConstructors cx dy
insertInner (Var x) c@(Sum _) cg    = insertSucc x c cg
insertInner c@(Con _ _) (Var y) cg  = insertPred c y cg
insertInner cx@(Con c cargs) (Sum ((d, dargs):ds)) cg
  | c == d                          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                       = insert cx (Sum ds) cg
insertInner (Sum cs) t cg           = foldM (\cg (c, cargs) -> insert (Con c cargs) t cg) cg cs

insertSucc :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => x -> SExpr x c -> ConGraphGen x c -> m (ConGraphGen x c)
insertSucc x sy cg@ConGraph{succs = s, subs = sb} =
  case sb M.!? x of
    Just z    -> insert z sy cg `throwContext` usingEquivalence x z
    otherwise ->
      case s M.!? x of
        Just ss ->
          if sy `elem` ss
            then return cg
            else do
              cg' <- closeSucc x sy cg{succs = M.insert x (sy:ss) s} `throwContext` fromClosure (Var x) sy
              case predChain cg' x sy [] of
                Just vs -> foldM (substitute sy) cg' vs `throwContext` fromCycle vs sy
                otherwise -> return cg'
        otherwise -> closeSucc x sy cg{succs = M.insert x [sy] s} `throwContext` fromClosure (Var x) sy

insertPred:: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => SExpr x c -> x -> ConGraphGen x c -> m (ConGraphGen x c)
insertPred sx y cg@ConGraph{preds = p, subs = sb} =
  case sb M.!? y of
    Just z    -> insert sx z cg  `throwContext` usingEquivalence y z
    otherwise ->
      case p M.!? y of
        Just ps ->
          if sx `elem` ps
            then return cg
            else do
              cg' <- closePred sx y cg{preds = M.insert y (sx:ps) p} `throwContext` fromClosure sx (Var y)
              case succChain cg' sx y [] of
                Just vs -> foldM (substitute sx) cg' vs `throwContext` fromCycle vs sx
                otherwise -> return cg'
        otherwise -> closePred sx y cg{preds = M.insert y [sx] p} `throwContext` fromClosure sx (Var y)

-- Partial online transitive closure
closeSucc :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => x -> SExpr x c -> ConGraphGen x c -> m (ConGraphGen x c)
closeSucc x sy cg =
  case preds cg M.!? x of
    Just ps   -> foldM (\cg p -> insert p sy cg) cg ps
    otherwise -> return cg

closePred :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => SExpr x c -> x -> ConGraphGen x c -> m (ConGraphGen x c)
closePred sx y cg =
  case succs cg M.!? y of
    Just ss   -> foldM (\cg s -> insert sx s cg) cg ss
    otherwise -> return cg

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
union :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => ConGraphGen x c -> ConGraphGen x c -> m (ConGraphGen x c)
union cg1@ConGraph{subs = sb} cg2@ConGraph{succs = s, preds = p, subs = sb'} = do
  -- Combine equivalence classes using left representation
  let msb  = M.union sb $ fmap subVar sb'

  -- Update cg1 with new equivalences
  cg1' <- M.foldrWithKey (\x se -> (>>= \cg -> substitute se cg x)) (return cg1) msb

  -- Insert edges from cg2 into cg1
  cg1'' <- M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert (Var k) v cg') cg vs)) (return cg1') s
  M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert v (Var k) cg') cg vs)) (return cg1'') p
  where
    subVar (Var x) = M.findWithDefault (Var x) x sb
    subVar (Sum cs) = Sum $ fmap (\(c, cargs) -> (c, fmap subVar cargs)) cs
    suBVar One = One

-- Safely substitute variable (x) with expression (se)
substitute :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => SExpr x c -> ConGraphGen x c -> x -> m (ConGraphGen x c)
substitute se ConGraph{succs = s, preds = p, subs = sb} x = do
  -- Necessary to recalculate preds and succs as se might not be a Var.
  -- If se is a Var this insures there are no redundant edges (i.e. x < x) or further simplifications.
  cg' <- case p' M.!? x of
    Just ps -> foldM (\cg pi -> insert pi se cg) cg ps
    Nothing -> return cg
  cg'' <- case s' M.!? x of
    Just ss -> foldM (\cg si -> insert se si cg) cg' ss
    Nothing -> return cg'
  return cg''{ succs = M.delete x $ succs cg'', preds = M.delete x $ preds cg''}
  where
    sub (Var y) | x == y = se
    sub (Sum cs) = Sum $ fmap (\(c, cargs) -> (c, fmap sub cargs)) cs
    sub One = One
    p'  = L.nub $ fmap (fmap sub) p
    s'  = L.nub $ fmap (fmap sub) s
    cg = ConGraph { succs = s', preds = p', subs = M.insert x se $ fmap sub sb }

-- Apply function to set expressions without effecting variables
graphMap :: (Eq c, Ord x, Constructor c) => (SExpr x c -> SExpr x c) -> ConGraphGen x c -> ConGraphGen x c
graphMap f cg@ConGraph{succs = s, preds = p, subs = sb} =
  ConGraph {
    succs = fmap (fmap f) s,
    preds = fmap (fmap f) p,
    subs = fmap f sb
  }
