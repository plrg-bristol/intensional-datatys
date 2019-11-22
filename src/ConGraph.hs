{-# LANGUAGE MultiParamTypeClasses #-}

module ConGraph (
      ConGraph (ConGraph, succs, preds, subs)
    , empty
    , fromList
    , toList

    , insert
    , substitute
    , substituteMany
    , union

    -- , closeScope
    , saturate
     ) where

import Control.Applicative hiding (empty)
import Control.Monad.RWS hiding (Sum)

import Data.Maybe
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
fromList :: [(Type, Type)] -> InferME ConGraph
fromList = foldM (\cg (t1, t2) -> insert t1 t2 cg) empty

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
      varMap (RVar (x, d, as)) = RVar (x, d, subTypeVar v t <$> as)




      
-- Normalise the constraints by applying recursive simplifications
normalise :: Type -> Type -> [(Type, Type)]
-- normalise t1 t2 | Core.pprTrace "normalise" (Core.ppr (t1, t2)) False = undefined
normalise t1@(Con e tc k as ts) t2@(V x d as') =
  let ts' = upArrowDataCon x k as
  in [(Con e tc k as ts', V x d as'), (Con e tc k as ts, Con e tc k as ts')]
normalise t1@(V x d as) t2@(Sum e tc as' cs) =
  let cs' = refineCon <$> cs
  in [(Sum e tc as' cs', Sum e tc as' cs), (V x d as, Sum e tc as' cs')]
  where
    refineCon (k, ts) = (k, upArrowDataCon x k as')
normalise t1 t2 = [(t1, t2)]

-- Insert new constraint with normalisation
insert :: Type -> Type -> ConGraph -> InferME ConGraph
insert t1 t2 _ | incomparable t1 t2 = do
  (e, _) <- ask
  Core.pprPanic "Sorts must algin" (Core.ppr (t1, t2, e)) undefined

-- insert t1 t2 _ | Core.pprTrace "insert" (Core.ppr (t1, t2)) False = undefined

insert Dot t2 cg = return cg -- Ignore any constriants concerning Dot, i.e. coercions
insert t1 Dot cg = return cg

insert t1 t2 cg@ConGraph{subs = sb} = foldM (\cg (t1', t2') -> insertInner (subRefinementMap sb t1') (subRefinementMap sb t2') cg) cg $ normalise t1 t2

-- Insert new constraint
insertInner :: Type -> Type -> ConGraph -> InferME ConGraph
insertInner x y cg | x == y = return cg

insertInner (t1 :=> t2) (t1' :=> t2') cg = do
  cg' <- insert t1' t1 cg
  insert t2 t2' cg'

insertInner t1@(Sum e1 tc as cs) t2@(Sum e2 tc' as' ds) cg | any (`notElem` fmap fst ds) $ fmap fst cs = do
  (e, _) <- ask
  Core.pprPanic "Invalid sum!" (Core.ppr (t1, t2, e1, e2, e, toList cg, M.toList (subs cg)))

insertInner cx@(Con _ _ c as cargs) dy@(Con _ _ d as' dargs) cg
  | c == d && as == as'          = foldM (\cg (ci, di) -> insert ci di cg) cg $ zip cargs dargs

insertInner cx@(Con _ tc c as cargs) (Sum e1 tc' as' ((d, dargs):ds)) cg
  | c == d && as == as' && tc == tc' = foldM (\cg (ci, di) -> insert ci di cg) cg $ zip cargs dargs
  | otherwise                        = insert cx (Sum e1 tc' as' ds) cg

insertInner vx@(Var x) vy@(Var y) cg
  | x > y                        = insertSucc x vy cg
  | otherwise                    = insertPred vx y cg

insertInner (Var x) c@Sum{} cg = insertSucc x c cg
insertInner c@Con{} (Var y) cg = insertPred c y cg

insertInner (Sum e tc as cs) t cg = foldM (\cg (c, cargs) -> insert (Con e tc c as cargs) t cg) cg cs

insertInner (App (TVar _) _) (App (TVar _) _) cg = return cg -- We already know these have the same sort and cannot inspect the tyvar

-- insertInner (TVar a) t cg = return $ subTypeVar a t cg

-- insertInner t (TVar a) cg = return $ subTypeVar a t cg

insertInner t1 t2 cg = do
  (e, _) <- ask
  Core.pprPanic "Unreduced type application in constraints!" (Core.ppr (t1, t2, e)) -- This should be unreachable

insertSucc :: RVar -> Type -> ConGraph -> InferME ConGraph
-- insertSucc x sy _ | Core.pprTrace "insertSucc" (Core.ppr (x, sy)) False = undefined
insertSucc x sy cg@ConGraph{succs = s} =
  case s M.!? x of
    Just ss ->
      if sy `elem` ss
        then return cg
        else do
          let cg' = cg{succs = M.insert x (sy:ss) s}
          -- cg' <- closeSucc x sy cg{succs = M.insert x (sy:ss) s}
          -- TODO: intersect sums
          case predChain cg' x sy [] of
            Just vs -> foldM (\cg x -> substitute x sy cg True) cg' vs
            _ -> return cg'
    _ -> return cg{succs = M.insert x [sy] s}
      -- closeSucc x sy cg{succs = M.insert x [sy] s}

insertPred :: Type -> RVar -> ConGraph -> InferME ConGraph
-- insertPred sx y _ | Core.pprTrace "insertPred" (Core.ppr (sx, y)) False = undefined
insertPred sx y cg@ConGraph{preds = p} =
  case p M.!? y of
    Just ps ->
      if sx `elem` ps
        then return cg
        else do
          let cg' = cg{preds = M.insert y (sx:ps) p}
          -- cg' <- closePred sx y cg{preds = M.insert y (sx:ps) p}
          -- TODO: union sums
          case succChain cg' sx y [] of
            Just vs -> foldM (\cg y -> substitute y sx cg True) cg' vs
            _ -> return cg'
    _ -> return cg{preds = M.insert y [sx] p}
      -- closePred sx y cg{preds = M.insert y [sx] p}

-- Partial online transitive closure
-- closeSucc :: RVar -> Type -> ConGraph -> InferME ConGraph
-- closeSucc x sy _ | Core.pprTrace "closeSucc" (Core.ppr (x, sy)) False = undefined
-- closeSucc x sy cg =
--   case preds cg M.!? x of
--     Just ps   -> foldM (\cg p -> insert p sy cg) cg ps
--     _ -> return cg

-- closePred :: Type -> RVar -> ConGraph -> InferME ConGraph
-- closePred sx y _ | Core.pprTrace "closePred" (Core.ppr (sx, y)) False = undefined
-- closePred sx y cg =
--   case succs cg M.!? y of
--     Just ss   -> foldM (\cg s -> insert sx s cg) cg ss
--     _ -> return cg

-- Partial online cycle elimination
predChain :: ConGraph -> RVar -> Type -> [RVar] -> Maybe [RVar]
-- predChain _ x t _ | Core.pprTrace "predChain" (Core.ppr (x, t)) False = undefined
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
-- succChain _ t x _ | Core.pprTrace "succChain" (Core.ppr (t, x)) False = undefined
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

-- Substitute many variables
substituteMany :: [RVar] -> [Type] -> ConGraph -> InferME ConGraph
substituteMany _ [] cg = return cg
substituteMany (r:rs) (t:ts) cg@ConGraph{succs = s, preds = p, subs = sb} = do
  -- Necessary to recalculate preds and succs as se might not be a Var.
  -- If se is a Var this insures there are no redundant edges (i.e. x < x) or further simplifications anyway
  let cg' = cg{ succs = M.map (fmap (subRefinementVar r t)) $ M.delete r s,
                      preds = M.map (fmap (subRefinementVar r t)) $ M.delete r p}

  cg'' <- case p M.!? r of
    Just ps -> foldM (\cg pi -> insert (subRefinementVar r t pi) t cg) cg' ps
    Nothing -> return cg'

  cg''' <- case s M.!? r of
    Just ss -> foldM (\cg si -> insert t (subRefinementVar r t si) cg) cg'' ss
    Nothing -> return cg''
  
  substituteMany rs ts cg'''

-- Safely substitute variable with an expression
substitute :: RVar -> Type -> ConGraph -> Bool -> InferME ConGraph
-- substitute x se _ t | Core.pprTrace "substitute" (Core.ppr (x, se, t)) False = undefined
substitute x se cg t | t && (x `elem` vars se) = return cg
substitute x se cg@ConGraph{succs = s, preds = p, subs = sb} t = do
  -- Necessary to recalculate preds and succs as se might not be a Var.
  -- If se is a Var this insures there are no redundant edges (i.e. x < x) or further simplifications anyway
  let cg' = ConGraph{ succs = M.map (fmap (subRefinementVar x se)) $ M.delete x s,
                      preds = M.map (fmap (subRefinementVar x se)) $ M.delete x p,
                      subs  = if t then M.insert x se (subRefinementVar x se <$> sb) else sb}

  cg'' <- case p M.!? x of
    Just ps -> foldM (\cg pi -> insert (subRefinementVar x se pi) se cg) cg' ps
    Nothing -> return cg'

  case s M.!? x of
    Just ss -> foldM (\cg si -> insert se (subRefinementVar x se si) cg) cg'' ss
    Nothing -> return cg''

-- Union of constraint graphs
union :: ConGraph -> ConGraph -> InferME ConGraph
-- union _ _ | Core.pprTrace "Union" (Core.ppr ()) False = undefined
union cg1@ConGraph{subs = sb} cg2@ConGraph{succs = s, preds = p, subs = sb'} = do
  -- Use cg1's representation
  let sb'' = subRefinementMap sb <$> sb'

  -- Check there are no cycles
  unless (null [(r, t)| (r@(RVar (x, _, _)), t) <- M.toList sb'', x `elem` stems t]) $ Core.pprPanic "Cyclic equivalences!" (Core.ppr ())

  -- Combine equivalence classes using left representation
  let msb  = M.union sb sb''

  -- Update cg1 with new equivalences
  cg1' <- substituteMany (M.keys msb) (M.elems msb) cg1

  -- Insert edges from cg2 into cg1
  cg1'' <- M.foldrWithKey (\k vs -> (>>= \cg -> foldM (flip (insert (Var k))) cg vs)) (return cg1') s
  M.foldrWithKey (\k vs -> (>>= \cg -> foldM (\cg' v -> insert v (Var k) cg') cg vs)) (return cg1'') p





-- The fixed point of normalisation and transitivity
saturate :: [Int] -> [Int] -> ConGraph -> InferM ([(Type, Type)], [(Type, Type)])
{-# INLINE saturate #-}
-- saturate _ _ cg | Core.pprTrace "saturate" (Core.ppr $ toList cg) False = undefined
saturate interface intermediate cg@ConGraph{subs = sb} = saturate' intermediate ([], toList cg)
  where
    unionUM :: [(Type, Type)] -> [(Type, Type)] -> [(Type, Type)]
    unionUM diff m = diff ++ [(a, b) | (a, b) <- m, a `notElem` map fst diff]

    -- Remove cycles of length one
    removeCycles :: ([(Type, Type)], [(Type, Type)]) -> ([(Type, Type)], [(Type, Type)])
    removeCycles (m, cs) = 
      let diff = [(a,  b) |
                  (a,  b)  <- cs,
                  (b', a') <- cs,
                  a == a',
                  b == b'] -- New cycles
      in
        (diff `unionUM` m, [(if x == a then b else x, if y == a then b else y) | (a, b) <- diff, (x, y) <- cs, x /= y])


    -- Remove intermediate nodes in sequence
    saturate' :: [Int] -> ([(Type, Type)], [(Type, Type)]) -> InferM ([(Type, Type)], [(Type, Type)])
    saturate' [] cs     = return $ saturate'' cs
    saturate' (n:ns) (m, cs) = do
      (_, rt, _) <- get
      let cs' = L.nub [(V x d' as, V x' d' as) | 
                       (V x d  as, V x' _  _ ) <- cs,
                       x /= x',
                       n `elem` [x, x'],
                       d' <- fromMaybe [] $ Core.lookupUFM rt d] -- Ensure all intermediate refinement variables ares suitably bound
                       ++ cs
          
      let diff = [ (d1', d2') |
                   (a, b) <- cs',
                   n `elem` stems b,
                   (b', c) <- cs',
                   a /= c,
                   b == b',
                   (d1, d2) <- normalise a c,
                   let (d1', d2') = (subRefinementMap sb d1, subRefinementMap sb d2),
                   (d1', d2') `notElem` cs']
      if null diff
        then 
          saturate' ns (m, [(a, b) | (a, b) <- cs', n `notElem` (stems a ++ stems b)])
        else do
          -- Add new edges
          let cs'' = L.nub diff ++ cs'

          -- Until a fixed point is reached
          saturate' (n:ns) (m, cs'')

    -- Saturate remaining interface nodes
    saturate'' (m, cs) =
      -- Normalise all transitive edges in cs and apply substitutions 
      let diff = [(d1', d2') | (a, b) <-cs, (b', c) <- cs,
                   b == b',
                   a /= c,
                   (d1, d2) <- normalise a c, 
                   let (d1', d2') = (subRefinementMap sb d1, subRefinementMap sb d2),
                   (d1', d2') `notElem` cs]

      in if null diff
          then removeCycles (m, cs) -- Remove trivial constraints
          else 
            -- Add new edges
            let cs' = L.nub diff ++ cs

            -- Until a fixed point is reached
            in saturate'' (m, cs')

-- Unsound/experimental optimisation:
-- Eagerly remove properly scoped bounded (intermediate) nodes
-- closeScope :: Int -> ConGraph -> InferME ConGraph
-- {-# INLINE closeScope #-}
-- closeScope scope cg@ConGraph{subs = sb} = return cg
-- closeScope scope cg@ConGraph{subs = sb} = do
--   (_, ctx) <- ask
--   let varTypes = M.elems $ var ctx
--   let envStems = concatMap (\(Forall _ ns cs t) -> [j | RVar (j, _, _, _) <- ns] ++ concat (concat [[stems c1, stems c2] | (c1, c2) <- cs]) ++ stems t) varTypes
  
--   -- Filter irrelevant variable, i.e. those that have gone out of scope
--   let p v = case v of {(V x _ _ _) ->  x <= scope {- || (x `elem` envStems) -}; _ -> True}

--   fromListWith $ [(n1, n2) | (n1, n2) <- saturate cg, p n1 || p n2]
--   where
--     fromListWith = foldM (\cg (t1, t2) -> insert t1 t2 cg) ConGraph{succs = M.empty, preds = M.empty, subs = sb}