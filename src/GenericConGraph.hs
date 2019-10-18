{-# LANGUAGE MultiParamTypeClasses #-}

module GenericConGraph
    (
    SExpr (Var, Con, Sum, One, Zero),
    Constructor (name, variance, args),
    ConGraphGen,
    empty,
    insert,
    substitute
    -- saturate,
    -- leastSolution
     ) where

import Control.Monad
import qualified Data.Map as M

-- Set expression with disjoint sum
data SExpr c x = Var x | Con (c x) | Sum [c x] | Zero | One

instance (Eq x, Constructor c x) => Eq (SExpr c x) where
  Var x == Var y   = x == y
  Con c == Con d   = name c == name d && args c == args d
  Sum cs == Sum ds = all (\(c, d) -> name c == name d) (zip cs ds)
  Zero == Zero     = True
  One == One       = True
  Sum [c] == Con d = name c == name d && args c == args d
  Con c == Sum [d] = name c == name d && args c == args d
  Zero == Sum []   = True
  Sum [] == Zero   = True
  _ == _           = False

-- Constructors are named and explicitly co- or contra- variant in arguments
-- length variance = length args
-- if name c == name d then length (args c) == length (args d)
class Constructor c x where
  name      :: c x -> String
  variance  :: c x -> [Bool]
  args      :: c x -> [SExpr c x]

-- Constraint graph
data ConGraphGen c x = ConGraphGen {
  succs :: M.Map x [SExpr c x],
  preds :: M.Map x [SExpr c x],
  subs  :: M.Map x (SExpr c x)
}

-- Empty constraint graph
empty :: ConGraphGen c x
empty = ConGraphGen { succs = M.empty, preds = M.empty, subs = M.empty }

-- Insert new constraint (subs ++ nub)
insert :: (Ord x, Constructor c x) => SExpr c x -> SExpr c x -> ConGraphGen c x -> Maybe (ConGraphGen c x)
insert vx@(Var x) vy@(Var y) cg
  | x == y                    = Just cg
  | x > y                     = insertSucc x vy cg
  | otherwise                 = insertPred vx y cg
insert _ One cg               = Just cg
insert Zero _ cg              = Just cg
insert (Con c) (Con d) cg
  | name c == name d          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg (zip3 (variance c) (args c) (args d))
  | otherwise                 = Nothing
insert (Con _) Zero _         = Nothing
insert One Zero _             = Nothing
insert One (Con _ ) _         = Nothing
insert (Var x) c@(Con _ ) cg  = insertSucc x c cg
insert c@(Con _) (Var y) cg   = insertPred c y cg
insert (Sum cs) t cg          = foldM (\cg c -> insert (Con c) t cg) cg cs
insert cx@(Con c) (Sum (d:ds)) cg
  | name c == name d          = foldM (\cg (v, ci, di) -> if v then insert ci di cg else insert di ci cg) cg (zip3 (variance c) (args c) (args d))
  | otherwise                 = insert cx (Sum ds) cg

insertSucc :: (Ord x, Constructor c x) => x -> SExpr c x -> ConGraphGen c x -> Maybe (ConGraphGen c x)
insertSucc x sy cg@ConGraphGen{succs = s, subs = sb} =
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

insertPred:: (Ord x, Constructor c x) => SExpr c x -> x -> ConGraphGen c x -> Maybe (ConGraphGen c x)
insertPred sx y cg@ConGraphGen{preds = p, subs = sb} =
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

-- Partial Online Transitive Closure
closeSucc :: (Ord x, Constructor c x) => x ->  SExpr c x -> ConGraphGen c x-> Maybe (ConGraphGen c x)
closeSucc x fy cg =
  case preds cg M.!? x of
    Just ps   -> foldM (\cg p -> insert p fy cg) cg ps
    otherwise -> return cg

closePred :: (Ord x, Constructor c x) => SExpr c x -> x -> ConGraphGen c x-> Maybe (ConGraphGen c x)
closePred fx y cg =
  case succs cg M.!? y of
    Just ss   -> foldM (\cg s -> insert s fx cg) cg ss
    otherwise -> return cg

-- Partial Online Cycle Elimination
predChain :: (Ord x, Constructor c x) => ConGraphGen c x -> x -> SExpr c x -> [x] -> Maybe [x]
predChain cg f (Var t) m = do
  guard $ f == t
  return $ t:m
predChain cg f t m = do
  ps <- preds cg M.!? f
  predLoop cg ps (f:m) f t  -- Inline as fold?

predLoop :: (Ord x, Constructor c x) => ConGraphGen c x -> [SExpr c x] -> [x] -> x -> SExpr c x -> Maybe [x]
predLoop _ [] _ _ _ = Nothing
predLoop cg ((Var p):ps) m f t =
  if p `elem` m || p > f
    then predLoop cg ps m f t
    else predChain cg p t m
predLoop cg (t':ps) m f t = do
  guard $ t == t'
  return m

succChain :: (Ord x, Constructor c x) => ConGraphGen c x -> SExpr c x -> x -> [x] -> Maybe [x]
succChain cg (Var f) t m = do
  guard $ f == t
  return $ f:m
succChain cg f t m = do
  ss <- succs cg M.!? t
  succLoop cg ss (t:m) f t  -- Inline as fold?

succLoop :: (Ord x, Constructor c x) => ConGraphGen c x -> [SExpr c x] -> [x] -> SExpr c x -> x -> Maybe [x]
succLoop _ [] _ _ _ = Nothing
succLoop cg ((Var s):ss) m f t =
  if s `elem` m || t <= s
    then succLoop cg ss m f t
    else succChain cg f s m
succLoop cg (f':ss) m f t = do
  guard $ f == f'
  return m

-- Collapse Cycle
-- Tidy
substitute :: (Ord x, Constructor c x) => SExpr c x -> ConGraphGen c x -> x -> Maybe (ConGraphGen c x)
substitute se ConGraphGen{succs = s, preds = p, subs = sb } x = do
  ps <- p' M.!? x
  cg'' <- foldM (\cg pi -> insert pi se cg) cg' ps

  ss <- s' M.!? x
  ConGraphGen { succs = s'', preds = p'', subs = sb'' } <- foldM (\cg si -> insert si se cg) cg'' ss

  return ConGraphGen { succs = M.delete x s'', preds = M.delete x p'', subs = sb'' }
  where
    cg' = ConGraphGen { succs = s', preds = p', subs = M.insert x se sb }
    p' = fmap (fmap sub) p
    s' = fmap (fmap sub) s
    sub (Var y) | x == y = se
    sub se' = se'

-- Least Solution
-- leastSolution :: (Eq c, Ord x, Constructor c) => ConGraphGen c x -> x -> [SExpr c x]
-- leastSolution cg@ConGraphGen{preds = p} x = case p M.!? x of
--   Just fs -> concatMap leastSolution' fs
--   otherwise -> []
--   where
--     leastSolution' (Var y) = leastSolution cg y
--     leastSolution' c@(Con _ _) = [c]

-- Saturate
-- saturate :: (Eq c, Ord x, Constructor c) => ConGraphGen c x -> [(SExpr c x, SExpr c x)]
