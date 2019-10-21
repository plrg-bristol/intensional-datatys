module ConGraph where

import Types
import Context
import Data.List hiding (insert, union)
import Data.Map.Strict as Map hiding (insert, foldr, union, partition)
import Control.Monad.Except
import Control.Monad.RWS hiding (Sum)
import Debug.Trace

data ConGraph =
  ConGraph {
    succs :: Map Type [Type], -- Map (String, Bool, String) (Set Type)
    preds :: Map Type [Type],
    subs  :: Map (String, Bool, String) Type
  }
  | GVar String (Map String Type) (Map (String, Bool, String) Type)
  | Union ConGraph ConGraph
  deriving (Eq, Show)

concreteConstraints :: ConGraph -> [(Type, Type)]
concreteConstraints (GVar _ _ _) = []
concreteConstraints (Union cg1 cg2) = concreteConstraints cg1 ++ concreteConstraints cg2
concreteConstraints cg1 = ConGraph.toList cg1

abstractConstraints :: ConGraph -> [(String, (Map String Type, Map (String, Bool, String) Type))]
abstractConstraints (GVar x tv rv) = [(x, (tv, rv))]
abstractConstraints (Union cg1 cg2) = abstractConstraints cg1 ++ abstractConstraints cg2
abstractConstraints _ = []

isGVar :: ConGraph -> Bool
isGVar (GVar _ _ _) = True
isGVar (Union cg1 cg2) = (isGVar cg1) && (isGVar cg2)
isGVar _ = False

instance Sub ConGraph where
  sub tv rv (GVar x tv' rv') = GVar x (mergeTV tv tv') (merge rv rv')
  sub tv rv (Union cg1 cg2) = Union (sub tv rv cg1) (sub tv rv cg2)
  sub tv rv cg = ConGraph {succs = succs', preds = preds', subs = subs'} -- Should this rebuild affected nodes?
    where
      succs' = mapKeys (sub tv rv) $ fmap (sub tv rv) $ succs cg
      preds' = mapKeys (sub tv rv) $ fmap (sub tv rv) $ preds cg
      subs'  = mapKeys subXD $ fmap (sub tv rv) $ subs cg

      subXD :: (String, Bool, String) -> (String, Bool, String)
      subXD (x, p, d) = case rv !? (x, p, d) of
        Just (RVar x' p' d') -> (x', p', d')
        otherwise -> (x, p, d)

-- Should this clean trivial maps and loops?
-- Rebuild affected nodes?
addSub :: String -> Bool -> String -> Type -> ConGraph -> ConGraph
addSub x p d t cg = let
  cg' = sub Map.empty (singleton (x, p, d) t) cg
  in case cg' of
    (GVar x tv rv) -> GVar x tv rv
    Union cg1 cg2 -> Union (mod cg1) (mod cg2)
    otherwise -> mod cg'
  where
    mod cg = cg{subs = unionWith const (singleton (x, p, d) t) $ subs cg}

empty :: ConGraph
empty = ConGraph {succs = Map.empty, preds = Map.empty, subs = Map.empty}

fromList :: [(Type, Type)] -> InferM ConGraph
fromList = foldM (\cg (t1, t2) -> insert t1 t2 cg) ConGraph.empty

toList :: ConGraph -> [(Type, Type)]
toList cg = [(k, v)|(k,vs) <- Map.toList (succs cg), v <- vs] ++ [(v, k)|(k,vs) <- Map.toList (preds cg), v <- vs]

-- Warning slow!
-- Inline
saturate :: [(Type, Type)] -> InferM [(Type, Type)]
saturate cg = do
  cg' <- ConGraph.fromList $ trans' cg
  return $ ConGraph.toList cg'
  where
    trans' closure
      | closure == closureUntilNow = closure
      | otherwise                  = trans' closureUntilNow
      where closureUntilNow =
              nub $ closure ++ [(a, c) | (a, b) <- closure, (b', c) <- closure, b == b']

-- Combine two subs with a preference for the first
-- Should this clean trivial maps and loops?
merge :: Map (String, Bool, String) Type -> Map (String, Bool, String) Type -> Map (String, Bool, String) Type
merge m1 m2 = let
  m2' = fmap (sub Map.empty m1) m2
  in unionWith const m1 m2'

mergeTV :: Map String Type -> Map String Type -> Map String Type
mergeTV m1 m2 = unionWith const m1 m2

-- Warning slow!
union :: ConGraph -> ConGraph -> InferM ConGraph
union g1@(GVar _ _ _) g2@(GVar _ _ _) = return $ Union g1 g2
union g1@(GVar _ _ _) g2@(Union cg1 cg2) = do
  x <- (union cg1 g1)
  return $ Union x cg2
union g1@(Union cg1 cg2) g2@(GVar _ _ _) = do
  x <- (union cg1 g2)
  return $ Union x cg2
union g1@(Union cg1 cg2) g2@(Union cg1' cg2') = do
  x <- union cg1 cg1'
  return $ Union x (Union cg2 cg2')
union cg1@ConGraph{succs = s1, preds = p1} g1@(GVar _ _ _) = return $ Union cg1 g1
union cg1@ConGraph{succs = s1, preds = p1} g2@(Union cg1' cg2') = do
  x <- union cg1 cg1'
  return $ Union x cg2'
union g1@(GVar _ _ _) cg1@ConGraph{succs = s1, preds = p1} = return $ Union cg1 g1
union g2@(Union cg1' cg2') cg1@ConGraph{succs = s1, preds = p1} = do
  x <- union cg1' cg1
  return $ Union x cg2'
union cg1@ConGraph{succs = s1, preds = p1} cg2@ConGraph{succs = s2, preds = p2} = do
  let subs' = merge (subs cg1) (subs cg2)
  let empty' = ConGraph.empty{subs = subs'}
  cg <- comb (sub Map.empty subs' cg1) [(k, v)|(k,vs) <- Map.toList s2, v <- vs]
  comb cg [(v, k)|(k,vs) <- Map.toList p2, v <- vs]
  where
    comb = foldM (\cg (t1, t2) -> insert t1 t2 cg)

-- Warning slow!
-- Should only apply to affected nodes see addSub
refresh :: ConGraph -> InferM ConGraph
refresh = union ConGraph.empty

insert, unsafeInsert', unsafeInsert'', unsafeInsert''' :: Type -> Type -> ConGraph -> InferM ConGraph
insert t1 t2 r@(GVar _ _ _) = do
  cg <- insert t1 t2 ConGraph.empty
  return $ Union cg r
insert t1 t2 r@(Union cg1 cg2) = if isGVar cg1 && (not $ isGVar cg2)
  then do
    cg2' <- insert t1 t2 cg2
    return $ Union cg1 cg2'
  else do
    cg1' <- insert t1 t2 cg1
    return $ Union cg1' cg2
-- Subs checking
insert t1 t2 cg = unsafeInsert (sub Map.empty (subs cg) t1) (sub Map.empty (subs cg) t2) cg

-- Loop checking
unsafeInsert t1 t2 cg
  | t1 == t2 = return cg
unsafeInsert t1 t2 cg = case succs cg !? t1 of
  Just ts -> if t2 `elem` ts
    then return cg
    else unsafeInsert' t1 t2 cg
  otherwise -> unsafeInsert' t1 t2 cg
unsafeInsert' t1 t2 cg = case preds cg !? t2 of
  Just ts -> if t1 `elem` ts
    then return cg
    else unsafeInsert'' t1 t2 cg
  otherwise -> unsafeInsert'' t1 t2 cg

-- Base Simplifications
unsafeInsert'' t1 t2@(TData d') cg = error "Data should not occur in constriant graph."
unsafeInsert'' t1@(TData d) t2 cg = error "Data should not occur in constriant graph."
unsafeInsert'' t1@(TBase b) t2@(TBase b') cg
  | b == b' = return cg
  | otherwise = throwError $ ConstraintError t1 t2 []
unsafeInsert'' t1@(TVar a) t2@(TVar a') cg
  | a == a' = return cg
  | otherwise = throwError $ ConstraintError t1 t2 []

-- Recursive Simplifications
unsafeInsert'' (t1 :=> t2) (t1' :=> t2') cg = do
  cg' <- insert t1' t1 cg
  insert t2 t2' cg'
unsafeInsert'' (Sum [Constructor k ts]) (Sum (Constructor k' ts':ks)) cg
  | k == k'   = foldM (flip $ uncurry insert) cg (zip ts ts')
  | otherwise = insert (Sum [Constructor k ts]) (Sum ks) cg
unsafeInsert'' t1@(Sum [Constructor k ts]) t2@(RVar x p d) cg = do
  ctx <- ask
  args <- delta p d k
  let ts' = upArrow x args
  if ts' /= ts
    then do
      cg' <- insert (Sum [Constructor k ts']) (RVar x p d) cg
      insert (Sum [Constructor k ts]) (Sum [Constructor k ts']) cg'
    else unsafeInsert''' t1 t2 cg
unsafeInsert'' t1@(RVar x p d) t2@(Sum cs) cg = do
  ctx <- ask
  s <- mapM (refineCon x d) cs
  if cs /= s
    then do
      cg' <- insert (Sum s) (Sum cs) cg
      insert (RVar x p d) (Sum s) cg'
    else unsafeInsert''' t1 t2 cg
  where
    refineCon :: String -> String -> Constructor -> InferM Constructor
    refineCon x d (Constructor k ts) = do
      args <- delta p d k
      return $ Constructor k (upArrow x args)

unsafeInsert'' (Sum ks) t cg
  | length ks > 1 = foldM (\cg' k-> insert (Sum [k]) t cg') cg ks

-- No Simplifications fall through
unsafeInsert'' t1 t2 cg = unsafeInsert''' t1 t2 cg

-- Partial Online Cycle Elimination
unsafeInsert''' t1 t2 cg = do
  let s = isSucc t1 t2
  if s
    then do
      cg' <- close s t1 t2 $ cg{succs = insertWith (++) t1 [t2] (succs cg)}
      case predChain cg' t1 t2 [] of
        (ts, True) -> case validCycle ts of
          Just t -> refresh $ collapseCycle ts t cg'
          otherwise -> throwError $ CycleError ts []
        otherwise  -> return cg'
    else do
      cg' <- close s t1 t2 $ cg{preds = insertWith (++) t2 [t1] (preds cg)}
      case succChain cg' t1 t2 [] of
        (ts, True) -> case validCycle ts of
          Just t -> refresh $collapseCycle ts t cg'
          otherwise -> throwError $ CycleError ts []
        otherwise  -> return cg'

-- Adds type equivalences to subs
collapseCycle :: [Type] -> Type -> ConGraph -> ConGraph
collapseCycle [] _ cg = cg
collapseCycle (RVar x p d:ts) t' cg = addSub x p d t' (collapseCycle ts t' cg)
collapseCycle (t:ts) t' cg
  | t == t' = collapseCycle ts t' cg

validCycle :: [Type] -> Maybe Type
validCycle [t] = Just t
validCycle (RVar x p d:ts) = do
  t' <- validCycle ts
  case t' of
    RVar x' p' d' -> do
      guard  (d == d')
      return $ RVar x p d
    otherwise -> Nothing
validCycle (t:ts) = do
  t' <- validCycle ts
  guard (t == t')
  return t

-- Partial Online Transitive Closure
close :: Bool -> Type -> Type -> ConGraph -> InferM ConGraph
close True t1 t2 cg = case preds cg !? t1 of
  Just ps -> foldM (\cg' p -> insert p t2 cg') cg ps
  otherwise -> return cg
close False t1 t2 cg = case succs cg !? t2 of
  Just ss -> foldM (\cg' s -> insert t1 s cg') cg ss
  otherwise -> return cg

isSucc :: Type -> Type -> Bool
isSucc (RVar x p _) (RVar y p' _) = x > y || (x == y && p > p')
isSucc (RVar _ _ _) (Sum _) = True
isSucc _ _ = False

predChain :: ConGraph -> Type -> Type -> [Type] -> ([Type], Bool)
predChain cg t1 t2 marked
  | t1 == t2  = (t1:marked, True)
  | otherwise = case preds cg !? t1 of
    Just ts   -> predLoop cg ts (t1:marked) t1 t2
    otherwise -> (marked, False)

predLoop :: ConGraph -> [Type] -> [Type] -> Type -> Type -> ([Type], Bool)
predLoop _ [] marked _ _ = (marked, False)
predLoop cg (p:ps) marked from to =
  if (not $ p `elem` marked) && not (isSucc p from)
    then let
      (marked', pc) = predChain cg p to marked
      in if pc
        then (marked', pc)
        else predLoop cg ps marked from to
      else predLoop cg ps marked from to

succChain :: ConGraph -> Type -> Type -> [Type] -> ([Type], Bool)
succChain cg t1 t2 marked
  | t1 == t2  = (t2:marked, True)
  | otherwise = case succs cg !? t2 of
    Just ts   -> succLoop cg ts (t2:marked) t1 t2
    otherwise -> (marked, False)

succLoop :: ConGraph -> [Type] -> [Type] -> Type -> Type -> ([Type], Bool)
succLoop _ [] marked _ _ = (marked, False)
succLoop cg (s:ss) marked from to =
  if (not $ s `elem` marked) && isSucc to s
    then let
      (marked', sc) = succChain cg from s marked
      in if sc
        then (marked', sc)
        else succLoop cg ss marked from to
      else succLoop cg ss marked from to
