{-# LANGUAGE PatternSynonyms, MultiParamTypeClasses, FunctionalDependencies #-}

module GenericConGraph (
      SExpr (Var, Con, Sum, One, Zero)
    , Constructor (variance)
    , ConGraphGen
    , ConstraintError (usingEquivalence, fromCycle, fromClosure, hetrogeneousConstructors, subtypeOfZero, supertypeOfOne)
    , Rewrite (toNorm)
    , empty
    , insert
    , union
    , substitute
    , graphMap
    , interface
     ) where

import Control.Monad
import Control.Monad.Except
import qualified Data.Map as M

-- Set expression with disjoint sum
data SExpr x c = Var x | Sum [(c, [SExpr x c])] | One

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
}

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
  hetrogeneousConstructors  :: c -> c -> e
  subtypeOfZero             :: SExpr x c -> e
  supertypeOfOne            :: SExpr x c -> e

-- Extend a thrown exception
throwContext :: MonadError e m => m a -> (e -> e) -> m a
throwContext ma f = ma `catchError` (throwError . f)

-- Additional deterministic rewriting rules for constriants
class Rewrite x c m where
  toNorm :: SExpr x c -> SExpr x c -> m [(SExpr x c, SExpr x c)]

-- Insert new constraint with rewriting rule
insert :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Ord x, Constructor c, Eq c) => SExpr x c -> SExpr x c -> ConGraphGen x c -> m (ConGraphGen x c)
insert t1 t2 cg = do
  cs <- toNorm t1 t2
  foldM (\cg (t1', t2') -> insertInner t1' t2' cg) cg cs

-- Insert new constraint
insertInner :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Ord x, Constructor c, Eq c) => SExpr x c -> SExpr x c -> ConGraphGen x c -> m (ConGraphGen x c)
insertInner vx@(Var x) vy@(Var y) cg
  | x == y                          = return cg
  | x > y                           = insertSucc x vy cg
  | otherwise                       = insertPred vx y cg
insertInner _ One cg                = return cg
insertInner Zero _ cg               = return cg
insertInner (Con c cargs) (Con d dargs) cg
  | c == d                          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                       = throwError $ hetrogeneousConstructors c d
insertInner t@(Con _ _) Zero _      = throwError $ subtypeOfZero t
insertInner t@One Zero _            = throwError $ subtypeOfZero t
insertInner One t@(Con _ _) _       = throwError $ supertypeOfOne t
insertInner (Var x) c@(Con _ _) cg  = insertSucc x c cg
insertInner c@(Con _ _) (Var y) cg  = insertPred c y cg
insertInner (Sum cs) t cg           = foldM (\cg (c, cargs) -> insert (Con c cargs) t cg) cg cs
insertInner cx@(Con c cargs) (Sum ((d, dargs):ds)) cg
  | c == d                          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                       = insert cx (Sum ds) cg

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
                Just xs -> foldM (substitute sy) cg' xs `throwContext` fromCycle xs sy
                otherwise -> return cg'
        otherwise -> return cg

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
                Just xs -> foldM (substitute sx) cg' xs `throwContext` fromCycle xs sx
                otherwise -> return cg'
        otherwise -> return cg

-- Partial online transitive closure
closeSucc :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => x -> SExpr x c -> ConGraphGen x c -> m (ConGraphGen x c)
closeSucc x fy cg =
  case preds cg M.!? x of
    Just ps   -> foldM (\cg p -> insert p fy cg) cg ps
    otherwise -> return cg

closePred :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => SExpr x c -> x -> ConGraphGen x c -> m (ConGraphGen x c)
closePred fx y cg =
  case succs cg M.!? y of
    Just ss   -> foldM (\cg s -> insert s fx cg) cg ss
    otherwise -> return cg

-- Partial online cycle elimination
predChain :: (Eq c, Ord x, Constructor c) => ConGraphGen x c -> x -> SExpr x c -> [x] -> Maybe [x]
predChain cg f (Var t) m = do
  guard $ f == t
  return $ m
predChain cg f t m = do
  ps <- preds cg M.!? f
  foldr predLoop Nothing ps
  where
    m' = f:m
    predLoop (Var p) pl =
      if p `elem` m' || p > f
        then pl
        else predChain cg p t m'
    predLoop t' _ = do
      guard $ t == t'
      return m'

succChain :: (Eq c, Ord x, Constructor c) => ConGraphGen x c -> SExpr x c -> x -> [x] -> Maybe [x]
succChain cg (Var f) t m = do
  guard $ f == t
  return $ m
succChain cg f t m = do
  ss <- succs cg M.!? t
  foldr succLoop Nothing ss
  where
    m' = t:m
    succLoop (Var s) sl =
      if s `elem` m' || t <= s
        then sl
        else succChain cg f s m'
    succLoop f' _ = do
      guard $ f == f'
      return m'

-- Union of constraint graphs
union :: (Rewrite x c m, MonadError e m, ConstraintError x c e, Eq c, Ord x, Constructor c) => ConGraphGen x c -> ConGraphGen x c -> m (ConGraphGen x c)
union cg1@ConGraph{subs = sb} cg2@ConGraph{succs = s, preds = p, subs = sb'} = do
  -- Combine equivalence classes using left representation
  let sb'' = fmap subVar sb'
  let cg1' = cg1{subs = M.union sb sb''}

  -- Update cg1 with new equivalences
  cg1'' <- M.foldrWithKey (\x se -> (>>= \cg -> substitute se cg x)) (return cg1') sb''

  -- Insert edges from cg2 into cg1
  cg1''' <- M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert (Var k) v cg') cg vs)) (return cg1'') s
  M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert v (Var k) cg') cg vs)) (return cg1''') p
  where
    subVar (Var x) = M.findWithDefault (Var x) x sb
    subVar se = se

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
    sub se' = se'
    p'  = fmap (fmap sub) p  -- nub
    s'  = fmap (fmap sub) s
    cg = ConGraph { succs = s', preds = p', subs = M.insert x se sb }

-- Apply function to set expressions without effecting variables
graphMap :: (Eq c, Ord x, Constructor c) => (SExpr x c -> SExpr x c) -> ConGraphGen x c -> ConGraphGen x c
graphMap f cg@ConGraph{succs = s, preds = p, subs = sb} =
  ConGraph {
    succs = fmap (fmap f) s,
    preds = fmap (fmap f) p,
    subs = fmap f sb
  }

-- Saturate the component of the graph which is determined by the function f
-- Warning slow!
interface :: (Eq c, Ord x, Constructor c) => (x -> Bool) -> ConGraphGen x c -> [(SExpr x c, SExpr x c)]
interface f cg@ConGraph{succs = s, preds = p} = filter (\(s1, s2) -> f' s1 && f' s2) $ transitiveClosure edges
  where
    edges = [(Var k, v)| (k, vs) <- M.toList s, v <- vs] ++ [(v, Var k)| (k, vs) <- M.toList p, v <- vs]
    f' (Var x) = f x
    f' (Sum cs) = all (\(c, cargs) -> all f' cargs) cs

    transitiveClosure closure
      | closure == closureUntilNow = closure
      | otherwise                  = transitiveClosure closureUntilNow
      where closureUntilNow =
              closure ++ [(a, c) | (a, b) <- closure, (b', c) <- closure, b == b']
