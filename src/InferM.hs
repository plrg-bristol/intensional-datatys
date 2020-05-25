{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module InferM
  ( InferM,
    Error,
    InferEnv (..),
    InferState (..),
    Context,
    mkSet,
    mkCon,
    fresh,
    branch,
    branch',
    isBranchReachable,
    topLevel,
    putVar,
    putVars,
    emit,
    setLoc,
    saturate,
    runInferM,
  )
where

import ConGraph
import Constraints
import Control.Monad.Except hiding (guard)
import Control.Monad.RWS hiding ((<>), guard)
import qualified Data.HashMap.Lazy as H
import qualified Data.IntMap as I
import qualified Data.List as L
import qualified Data.Map as M
import DataTypes
import GhcPlugins hiding (L, Type, empty)
import Guards
import Scheme
import Types
import Prelude hiding ((<>))

data Error
  = forall a b.
    Error
      { collision :: SrcSpan,
        constraint :: (DataType Name, K a, K b)
      }

instance Outputable Error where
  ppr Error {collision = c, constraint = (_, l, r)} =
    text "The constructor: " <> ppr l <> text ", arising at: " <> ppr (constraintLoc l)
      <> text ", can colide with the pattern: "
      <> ppr r
      <> text ", arising at: "
      <> ppr (constraintLoc r)
      <> text ", when in the function: "
      <> ppr c

-- The inference monad
type InferM s m = RWST (InferEnv s) [Error] (InferState s) m

data InferEnv s
  = InferEnv
      { unrollDataTypes :: Bool,
        allowContra :: Bool,
        modName :: Module,
        branchPath :: Path,
        branchGuard :: GuardSet s,
        varEnv :: Context s,
        inferLoc :: SrcSpan
      }

data InferState s
  = InferState
      { freshRVar :: RVar,
        congraph :: ConGraph s,
        -- Binary decision diagram state
        memo :: H.HashMap (Memo s) (GuardSet s),
        freshId :: ID,
        nodes :: I.IntMap (Node s),
        hashes :: H.HashMap (Node s) ID
      }

instance Monad m => GsM (InferState s) s (InferM s m) where
  lookupNode i =
    gets (I.lookup i . nodes) >>= \case
      Nothing -> error ("No node with that ID!" ++ show i)
      Just n -> return n
  lookupHash n = gets (H.lookup n . hashes)
  freshNode n = do
    s@InferState {nodes = ns, hashes = hs, freshId = i} <- get
    put
      s
        { freshId = i + 1,
          nodes = I.insert i n ns,
          hashes = H.insert n i hs
        }
    return i
  memo op a =
    gets (H.lookup op . InferM.memo) >>= \case
      Nothing -> do
        r <- a
        modify (\s -> s {InferM.memo = H.insert op r (InferM.memo s)})
        return r
      Just r -> return r

-- A fresh refinement variable
fresh :: Monad m => InferM s m RVar
fresh = do
  s@InferState {freshRVar = i} <- get
  put s {freshRVar = i + 1}
  return i

-- Make constructors tagged by the current location
mkCon :: Monad m => DataCon -> InferM s m (K 'L)
mkCon k = do
  l <- asks inferLoc
  return (Con (getName k) l)

mkSet :: Monad m => [DataCon] -> InferM s m (K 'R)
mkSet ks = do
  l <- asks inferLoc
  return (Set (mkUniqSet (getName <$> ks)) l)

-- The environment variables and their types
type Context s = M.Map Name (Scheme s)

instance GsM state s m => Refined (Context s) m where
  domain = foldM (\k -> fmap (L.union k) . domain) []
  rename x = mapM . rename x

-- Insert variables into environment
putVar :: Monad m => Name -> Scheme s -> InferM s m a -> InferM s m a
putVar n s = local (\env -> env {varEnv = M.insert n s (varEnv env)})

putVars :: Monad m => Context s -> InferM s m a -> InferM s m a
putVars ctx = local (\env -> env {varEnv = M.union ctx (varEnv env)})

-- A Path records the terms that have been matched against in the current path
type Path = [(CoreExpr, [DataCon])]

-- Check if an expression is in the path
topLevel :: Monad m => CoreExpr -> InferM s m Bool
topLevel e = asks (foldr (\(e', _) es -> not (cheapEqExpr e e') && es) True . branchPath)

-- Check if a branch is possible, i.e. doesn't contradict the current branch
isBranchReachable :: Monad m => CoreExpr -> DataCon -> InferM s m Bool
isBranchReachable e k = asks (foldr (\(e', ks) es -> (not (cheapEqExpr e e') || k `elem` ks) && es) True . branchPath)

-- Locally guard constraints and add expression to path
branch :: Monad m => CoreExpr -> [DataCon] -> RVar -> DataType TyCon -> InferM s m a -> InferM s m a
branch e ks x d m = do
  curr_guard <- asks branchGuard
  new_guard <-
    dom (getName <$> ks) x (getName <$> d)
      >>= (&&& curr_guard)
  local
    ( \env ->
        env
          { branchGuard = new_guard,
            branchPath = (e, ks) : branchPath env
          }
    )
    m

-- Locally guard constraints without an associated core expression
branch' :: Monad m => [DataCon] -> RVar -> DataType TyCon -> InferM s m a -> InferM s m a
branch' ks x d m = do
  curr_guard <- asks branchGuard
  new_guard <-
    dom (getName <$> ks) x (getName <$> d)
      >>= (&&& curr_guard)
  local
    ( \env ->
        env
          { branchGuard = new_guard
          }
    )
    m

setLoc :: Monad m => RealSrcSpan -> InferM s m a -> InferM s m a
setLoc l = local (\env -> env {inferLoc = RealSrcSpan l})

emit :: Monad m => K l -> K r -> DataType TyCon -> InferM s m ()
emit k1 k2 d
  | not (trivial (orig d) || full k2) =
    case toAtomic k1 k2 of
      Nothing -> do
        l <- asks inferLoc
        tell [Error l (getName <$> d, k1, k2)]
      Just cs -> do
        cg <- gets congraph
        g <- asks branchGuard
        cg' <- foldM (\cg' (k1', k2') -> insert k1' k2' g (getName <$> d) cg') cg cs
        modify (\s -> s {congraph = cg'})
  | otherwise = return ()
  where
    full :: K r -> Bool
    full (Set ks _) = nonDetEltsUniqSet ks == fmap getName (tyConDataCons (orig d))
    full (Con k _) = [k] == fmap getName (tyConDataCons (orig d))
    full _ = False

runInferM ::
  Monad m =>
  (forall s. InferM s m a) ->
  Bool ->
  Bool ->
  Module ->
  M.Map Name (SchemeGen (Type 'T) IfConGraph) ->
  m (a, [Error])
runInferM run unroll allow_contra mod_name init_env =
  evalRWST
    ( do
        env <- mapM (\(Scheme tyvs dvs t g) -> Scheme tyvs dvs t <$> mapM (mapM fromList) g) init_env
        local (\e -> e {varEnv = env}) run
    )
    (InferEnv unroll allow_contra mod_name [] Top M.empty (UnhelpfulSpan (mkFastString "Top level")))
    (InferState 0 empty H.empty 0 I.empty H.empty)

-- Transitively remove local constraints and attach them to variables
saturate :: Monad m => Context s -> InferM s m (Context s)
saturate ts = do
  interface <- domain ts
  runExceptT
    ( do
        cg <- lift $ gets congraph
        restrict interface cg
    )
    >>= \case
      Left e -> do
        l <- asks inferLoc
        tell [Error {collision = l, constraint = e}]
        modify (\s -> s {InferM.memo = H.empty, hashes = H.empty, congraph = empty})
        -- Continue ignoring the constraints from this recursive group
        return ((\s -> s {boundvs = interface, constraints = Nothing}) <$> ts)
      Right cg' -> do
        modify (\s -> s {InferM.memo = H.empty, hashes = H.empty, congraph = empty})
        return ((\s -> s {boundvs = interface, constraints = Just cg'}) <$> ts)