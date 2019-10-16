{-# LANGUAGE RankNTypes #-}

module Inference where

import Types
import Expr
import Resolve
import Context
import ConGraph
import Data.List hiding (filter, union, insert)
import Data.Map.Strict as Map hiding (filter, insert, foldr, map, union, partition)
import Control.Monad.RWS hiding (Sum, Alt)
import Control.Monad.Except
import Debug.Trace

newInt :: InferM Int
newInt = do
    i <- get
    put (i + 1)
    return i

fresh :: Sort -> InferM Type
fresh t = do
    i <- newInt
    return $ head $ upArrow (show i) [polarise True t]

freshScheme :: SortScheme -> InferM TypeScheme
freshScheme (SForall as s) = do
    i <- newInt
    j <- newInt
    return $ Forall as [] (GVar (show j) Map.empty Map.empty) $ head $ upArrow (show i) [polarise True s]

-- Inline with saturate
interface :: [String] -> [(Type, Type)] -> [(Type, Type)]
interface rs cg = filter f cg
  where
    rvar' t = fmap (\(x, _, _) -> x) $ nub $ rvars t
    f (t1, t2) = all (`elem` rs) (rvar' t1 ++ rvar' t2)

rvars :: Type -> [(String, Bool, String)]
rvars (TVar _)  = []
rvars (TBase _) = []
rvars (TData _) = []
rvars (RVar x p d) = [(x, p, d)]
rvars (t1 :=> t2) = rvars t1 ++ rvars t2
rvars (Sum k) = concat [rvars t | Constructor s ts <- k, t <- ts]

tvars :: Type -> [String]
tvars (TVar a) = [a]
tvars (TBase _) = []
tvars (TData _) = []
tvars (RVar _ _ _) = []
tvars (t1 :=> t2) = tvars t1 ++ tvars t2
tvars (Sum k) = concat [tvars t | Constructor s ts <- k, t <- ts]

toTypeScheme :: Type -> [(Type, Type)] -> ([String], [(String, Bool, String)], [(Type, Type)], Type)
toTypeScheme t cg = (tvars t, rvs, interface xs cg, t)
  where
    -- These don't need to be fresh as each inference will use new numbers
    rvs = nub $ rvars t
    xs = fmap (\(x,_,_) -> x) rvs

inferModule :: Module -> InferM [(String, ([String], [(String, Bool, String)], [(Type, Type)], Type))]
inferModule m = do
  m' <- inferModule' m
  m'' <- resolve m'
  return [(x, toTypeScheme t cg) | (x, t, cg) <- m'']
  where
    inferModule' :: Module -> InferM [(String, Type, ConGraph)]
    inferModule' [] = return []
    inferModule' ((x,ss,e):bs) = do
      g <- gamma
      (t, cg) <- local (uncurry insertMany (unzip g)) $ infer e
      cgc <- inferModule' bs
      let (Forall _ _ (GVar y _ _) _) = (Map.fromList g) ! x
      return $ (y, t, cg) : cgc

    gamma = mapM (\(x, ss, e) -> do {ts <- freshScheme ss; return (x, ts)}) m

infer :: Expr -> InferM (Type, ConGraph)
infer e@(ECst c) = do
  t <- safeCst c `inExpr` e
  t' <- fresh t
  return (t', ConGraph.empty)

infer e@(ECon k) = do
  (d, args) <- safeCon k `inExpr` e
  ts <- mapM fresh args
  x  <- fresh $ SData d
  cg <- insert (Sum [Constructor k ts]) x ConGraph.empty `inExpr` e
  return (foldr (:=>) x ts, cg)

infer e@(EVar x ts) = do
  sx <- safeVar x `inExpr` e
  case sx of
    Nothing -> if length ts == 0
      then infer (ECon x)   -- GHC Core doesn't represent constructors differently
      else throwError $ VarError x []
    Just (Forall as xs cs u) -> do
      if length as /= length ts
        then throwError $ TSError x (length as) (length ts) [e]
        else do
          ys  <- mapM fresh $ map (\(x, p, d)-> SData d) xs
          ts' <- mapM fresh ts
          let tv = Map.fromList $ zip as ts'
          let rv = Map.fromList $ zip xs ys
          let u' = sub tv rv u
          v   <- getSort u'
          v'  <- fresh v
          cs'  <- insert u' v' cs `inExpr` e
          let cs'' = sub tv rv cs'
          return (v', cs'')

infer e'@(EAbs x t e) = do
  t1       <- fresh t
  (t2, cg) <- local (insertVar x $ Forall [] [] ConGraph.empty t1) (infer e) `inExpr` e'
  return (t1 :=> t2, cg)

infer e'@(EApp e1 e2) = do
  (t1, c1) <- infer e1 `inExpr` e'
  (t2, c2) <- infer e2 `inExpr` e'
  case t1 of
    t3 :=> t4 -> do
      cg  <- c1 `union` c2
      cg' <- insert t2 t3 cg `inExpr` e'
      return (t4, cg')
    -- (RVar s d) -> do
    --   t3 <- fresh
    --   t4 <- fresh
    --   let sub' :: forall a. Sub a => a -> a
    --       sub' = sub Map.empty (singleton (s, d) $ t3 :=> t4)
    --   cg <- insert (sub' t3) t1 (union (sub' c1) (sub' c2)) `inExpr` e'
    --   return (t4, cg)
    otherwise -> throwError $ AppError [e', e1]

-- Literal patterns
infer e'@(ECase e n et rt as) = do
  et' <- fresh et
  (t0, c0) <- infer e `inExpr` e'
  local (insertVar n $ Forall [] [] ConGraph.empty et') $ do
    if length as == 0
      then throwError $ EmptyCaseError [e']
      else let
        (alts, def) = partition aCon as
        in case def of

          [Default d] -> do
            (td, cd) <- infer d `inExpr` e'
            hyp <- mapM inferAlt alts `inExpr` e'
            let (kis, bTis, tis', cis') = unzip4 hyp
            t        <- fresh rt
            cg       <- foldM union ConGraph.empty (cd:cis')
            cg'      <- ConGraph.fromList ((td, t):[(ti', t) | ti' <- tis'])
            cg''     <- cg `union` cg'
            cg'''   <- cg'' `union` c0
            return (t, cg''')

          [] -> do
            hyp <- mapM inferAlt alts `inExpr` e'
            let (kis, bTis, tis', cis') = unzip4 hyp
            t        <- fresh rt
            cg       <- foldM union ConGraph.empty $ cis'
            cg'      <- ConGraph.fromList [(ti', t) | ti' <- tis']
            cg''     <- cg `union` cg'
            cg'''    <- insert t0 (Sum [Constructor ki bTi | (ki, bTi) <- zip kis bTis]) cg''
            cg''''   <- cg''' `union` c0
            return (t, cg'''')

          otherwise -> throwError $ DoubleDefaultError [e']

-- Local module
-- inferLet e'@(ELet xs e2) = do
--   gamma <- inferModule xs
--   local ((uncurry insertMany) (unzip $ gamma)) $ infer e2

inferAlt :: Alt -> InferM (String, [Type], Type, ConGraph)
inferAlt a@(ACon ki bxi ei) = do
  (_, args) <- safeCon ki `inAlt` a
  if length args == length bxi
    then do
      bTi <- mapM fresh args
      local (insertMany bxi (map (Forall [] [] ConGraph.empty) bTi)) $ do
        (ti', ci) <- infer ei `inAlt` a
        return (ki, bTi, ti', ci)
    else (throwError $ PatternError []) `inAlt` a

getSort :: Type -> InferM Sort
getSort (TVar a) = return $ SVar a
getSort (TBase a) = return $ SBase a
getSort (TData d) = return $ SData d
getSort (RVar x p d) = return $ SData d
getSort (t1 :=> t2) = do
  s1 <- getSort t1
  s2 <- getSort t2
  return $ SArrow s1 s2
getSort (Sum (Constructor k _:_)) = do
  (d, _) <- safeCon k
  return $ SData d

-- Legacy code from implicitly typed case statements, not necessary in GHC core
-- meet :: Type -> Type -> Maybe Type
-- meet Void t = Just t
-- meet t Void = Just t
-- meet (TVar a) (TVar a')
--   | a == a' = Just $ TVar a
-- meet (TBase b) (TBase b')
--   | b == b' = Just $ TBase b
-- meet (TData d) (TData d')
--   | d == d' = Just $ TData d
-- meet (t1 :=> t2) (t1' :=> t2') = do
--   m1 <- meet t1 t1'
--   m2 <- meet t2 t2'
--   return $ m1 :=> m2
-- meet (Sum ks) (Sum ks') = fmap Sum $ meetSum ks ks'
-- meet (RVar x d) (RVar x' d')
--   | d == d' = Just $ RVar x d
-- meet (RVar x d) (TData d')
--   | d == d' = Just $ TData d
-- meet _ _ = Nothing
--
-- meetSum :: [Constructor] -> [Constructor] -> Maybe [Constructor]
-- meetSum [] [] = Just []
-- meetSum (a:as) (b:bs) = do
--   m <- meetCon a b
--   ms <- meetSum as bs
--   return $ m:ms
-- meetSum _ _ = Nothing
--
-- meetCon :: Constructor -> Constructor -> Maybe Constructor
-- meetCon (Constructor k ts) (Constructor k' ts')
--   | k == k' = fmap (Constructor k) $ mapM (uncurry meet) (zip ts ts')
-- meetCon _ _ = Nothing
