module GenericConGraph (
      SExpr (Var, Con, Sum, One, Zero)
    , Constructor (variance)
    , ConGraphGen
    , empty
    , insert
    , union
    , substitute
    , graphMap
    -- , saturate
    -- , leastSolution
     ) where

import Control.Monad
import qualified Data.Map as M

-- Set expression with disjoint sum
data SExpr x c = Var x | Con c [SExpr x c] | Sum [(c, [SExpr x c])] | Zero | One

instance (Eq c, Eq x) => Eq (SExpr x c) where
  Var x == Var y                  = x == y
  Con c cargs == Con d dargs      = c == d && cargs == dargs
  Con c cargs == Sum [(d,dargs)]  = c == d && cargs == dargs
  Sum [(c, cargs)] == Con d dargs = c == d && cargs == dargs
  Sum cs == Sum ds                = all (uncurry (==)) $ zip cs ds
  Sum [] == Zero                  = True
  Zero == Sum []                  = True
  Zero == Zero                    = True
  One == One                      = True
  _ == _                          = False

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

-- Insert new constraint
insert :: (Eq c, Ord x, Constructor c) => SExpr x c -> SExpr x c -> ConGraphGen x c -> Maybe (ConGraphGen x c)
insert vx@(Var x) vy@(Var y) cg
  | x == y                    = Just cg
  | x > y                     = insertSucc x vy cg
  | otherwise                 = insertPred vx y cg
insert _ One cg               = Just cg
insert Zero _ cg              = Just cg
insert (Con c cargs) (Con d dargs) cg
  | c == d                    = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                 = Nothing
insert (Con _ _) Zero _       = Nothing
insert One Zero _             = Nothing
insert One (Con _ _) _        = Nothing
insert (Var x) c@(Con _ _) cg = insertSucc x c cg
insert c@(Con _ _) (Var y) cg = insertPred c y cg
insert (Sum cs) t cg          = foldM (\cg (c, cargs) -> insert (Con c cargs) t cg) cg cs
insert cx@(Con c cargs) (Sum ((d, dargs):ds)) cg
  | c == d                    = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg $ zip3 (variance c) cargs dargs
  | otherwise                 = insert cx (Sum ds) cg

insertSucc :: (Eq c, Ord x, Constructor c) => x -> SExpr x c -> ConGraphGen x c -> Maybe (ConGraphGen x c)
insertSucc x sy cg@ConGraph{succs = s, subs = sb} =
  case sb M.!? x of
    Just z    -> insert z sy cg
    otherwise ->
      case s M.!? x of
        Just ss ->
          if sy `elem` ss
            then return cg
            else do
              cg' <- closeSucc x sy cg{succs = M.insert x (sy:ss) s}
              xs <- predChain cg' x sy []
              foldM (substitute sy) cg' xs
        otherwise -> return cg

insertPred:: (Eq c, Ord x, Constructor c) => SExpr x c -> x -> ConGraphGen x c -> Maybe (ConGraphGen x c)
insertPred sx y cg@ConGraph{preds = p, subs = sb} =
  case sb M.!? y of
    Just z    -> insert sx z cg
    otherwise ->
      case p M.!? y of
        Just ps ->
          if sx `elem` ps
            then return cg
            else do
              cg' <- closePred sx y cg{preds = M.insert y (sx:ps) p}
              xs <- succChain cg' sx y []
              foldM (substitute sx) cg' xs
        otherwise -> return cg

-- Partial online transitive closure
closeSucc :: (Eq c, Ord x, Constructor c) => x ->  SExpr x c -> ConGraphGen x c-> Maybe (ConGraphGen x c)
closeSucc x fy cg =
  case preds cg M.!? x of
    Just ps   -> foldM (\cg p -> insert p fy cg) cg ps
    otherwise -> return cg

closePred :: (Eq c, Ord x, Constructor c) => SExpr x c -> x -> ConGraphGen x c-> Maybe (ConGraphGen x c)
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
union :: (Eq c, Ord x, Constructor c) => ConGraphGen x c -> ConGraphGen x c -> Maybe (ConGraphGen x c)
union cg1@ConGraph{subs = sb} cg2@ConGraph{succs = s, preds = p, subs = sb'} = do
  -- Combine equivalence classes using left representation
  let sb'' = fmap subVar sb'
  let cg1' = cg1{subs = M.union sb sb''}

  -- Update cg1 with new equivalences
  cg1'' <- M.foldrWithKey (\x se -> (>>= \cg -> substitute se cg x)) (Just cg1') sb''

  -- Insert edges from cg2 into cg1
  cg1''' <- M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert (Var k) v cg') cg vs)) (Just cg1'') s
  M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert v (Var k) cg') cg vs)) (Just cg1''') p
  where
    subVar (Var x) = M.findWithDefault (Var x) x sb
    subVar se = se

-- Safely substitute variable (x) with expression (se)
substitute :: (Eq c, Ord x, Constructor c) => SExpr x c -> ConGraphGen x c -> x -> Maybe (ConGraphGen x c)
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
graphMap :: (Eq c, Ord x, Constructor c) => (SExpr x c -> SExpr x c) -> ConGraphGen x c -> Maybe (ConGraphGen x c)
graphMap f cg@ConGraph{succs = s, preds = p, subs = sb} = return $
  ConGraph {
    succs = fmap (fmap f) s,
    preds = fmap (fmap f) p,
    subs = fmap f sb
  }

-- Least solution
-- leastSolution :: (Eq c, Ord x, Constructor c) => ConGraphGen x c -> x -> [SExpr x c]
-- leastSolution cg@ConGraphGen{preds = p} x = case p M.!? x of
--   Just fs -> concatMap leastSolution' fs
--   otherwise -> []
--   where
--     leastSolution' (Var y) = leastSolution cg y
--     leastSolution' c@(Con _ _) = [c]

-- Saturate
-- saturate :: (Eq c, Ord x, Constructor c) => ConGraphGen x c -> [(SExpr x c, SExpr x c)]
