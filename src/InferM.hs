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
    branchAny,
    branchWithoutExpr,
    isBranchReachable,
    topLevel,
    putVar,
    putVars,
    emit,
    setLoc,
    InferM.saturate,
    runInferM,
  )
where

import Constraints
import Constructors
import Control.Monad.Except hiding (guard)
import Control.Monad.RWS hiding ((<>), guard)
import qualified Data.HashMap.Lazy as H
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import Data.Maybe
import DataTypes
import GhcPlugins hiding (L, Type, empty)
import Scheme
import Types
import Prelude hiding ((<>))

data Error where
  Error :: Constraint l r -> Error
  -- Log :: RVar -> SrcSpan -> Error

instance Outputable Error where
  -- ppr (Log x i) = text "logged: " <> ppr (x, i)
  ppr (Error c) = ppr c

-- The inference monad
type InferM = RWS InferEnv [Error] InferState

data InferEnv
  = InferEnv
      { modName :: Module,
        branchPath :: Path,
        branchGuard :: Guard,
        varEnv :: Context,
        inferLoc :: SrcSpan
      }

data InferState
  = InferState
      { freshRVar :: RVar,
        constraints :: ConstraintSet
        -- Binary decision diagram state
        -- memo :: H.HashMap (Memo s) (GuardSet s),
        -- freshId :: ID,
        -- nodes :: I.IntMap (Node s),
        -- hashes :: H.HashMap (Node s) ID
      }

-- instance GsM (InferState s) s (InferM s) where
--   lookupNode i =
--     gets (I.lookup i . nodes) >>= \case
--       Nothing -> error ("No node with that ID!" ++ show i)
--       Just n -> return n
--   lookupHash n = gets (H.lookup n . hashes)
--   freshNode n = do
--     s@InferState {nodes = ns, hashes = hs, freshId = i} <- get
--     put
--       s
--         { freshId = i + 1,
--           nodes = I.insert i n ns,
--           hashes = H.insert n i hs
--         }
--     return i
--   lookupMemo op = gets (H.lookup op . InferM.memo)
--   insertMemo op r = modify (\s -> s {InferM.memo = H.insert op r (InferM.memo s)})

-- A fresh refinement variable
fresh :: InferM RVar
fresh = do
  s@InferState {freshRVar = i} <- get
  put s {freshRVar = i + 1}
  l <- asks inferLoc
  -- tell [Log i l]
  return i

-- Make constructors tagged by the current location
mkCon :: DataCon -> InferM (K 'L)
mkCon k = do
  l <- asks inferLoc
  return (Con (getName k) l)

mkSet :: [DataCon] -> InferM (K 'R)
mkSet ks = do
  l <- asks inferLoc
  return (Set (mkUniqSet (getName <$> ks)) l)

-- The environment variables and their types
type Context = M.Map Name Scheme

instance Refined Context where
  domain = foldr (IS.union . domain) IS.empty
  rename x = fmap . rename x

-- Insert variables into environment
putVar :: Name -> Scheme -> InferM a -> InferM a
putVar n s = local (\env -> env {varEnv = M.insert n s (varEnv env)})

putVars :: Context -> InferM a -> InferM a
putVars ctx = local (\env -> env {varEnv = M.union ctx (varEnv env)})

-- A Path records the terms that have been matched against in the current path
type Path = [(CoreExpr, DataCon)]

-- Check if an expression is in the path
topLevel :: CoreExpr -> InferM Bool
topLevel e = asks (foldr (\(e', _) es -> not (cheapEqExpr e e') && es) True . branchPath)

-- Check if a branch is possible, i.e. doesn't contradict the current branch
isBranchReachable :: CoreExpr -> DataCon -> InferM Bool
isBranchReachable e k = asks (foldr (\(e', k') es -> (not (cheapEqExpr e e') || k == k') && es) True . branchPath)

-- Locally guard constraints and add expression to path
branch :: CoreExpr -> DataCon -> RVar -> Level -> InferM a -> InferM a
branch e k x l m = do
  curr_guard <- asks branchGuard
  path <- asks branchPath
  local
    ( \env ->
        env
          { branchGuard = IM.insertWith (H.unionWith unionUniqSets) x (H.singleton l (unitUniqSet (getName k))) curr_guard,
            branchPath = (e, k) : path
          }
    )
    m

-- Locally guard constraints and add expression to path
branchAny :: CoreExpr -> [DataCon] -> RVar -> Level -> InferM a -> InferM ()
branchAny e ks x l m = mapM_ (\k -> branch e k x l m) ks

-- Locally guard constraints without an associated core expression
branchWithoutExpr :: DataCon -> RVar -> Level -> InferM a -> InferM a
branchWithoutExpr k x l m = do
  curr_guard <- asks branchGuard
  local
    ( \env ->
        env
          { branchGuard = IM.insertWith (H.unionWith unionUniqSets) x (H.singleton l (unitUniqSet (getName k))) curr_guard
          }
    )
    m

setLoc :: RealSrcSpan -> InferM a -> InferM a
setLoc l = local (\env -> env {inferLoc = RealSrcSpan l})

emit :: K l -> K r -> InferM ()
emit k1 k2 = do
  -- | not (trivial (orig d) || full (cons k2) (orig d)) = do
    l <- asks inferLoc
    g <- asks branchGuard
    case toAtomic k1 k2 of
      Nothing -> tell [Error Constraint { left = k1, right = k2, Constraints.srcSpan = l, guard = g}]
      Just cs -> do
        cg <- gets InferM.constraints
        let cg' =
              foldr
                ( \(k1', k2') ->
                    insert
                      Constraint
                        { left = k1',
                          right = k2',
                          guard = g,
                          Constraints.srcSpan = l
                        }
                )
                cg
                cs
        modify (\s -> s {InferM.constraints = cg'})
  -- | otherwise = return ()

full :: [Name] -> TyCon -> Bool
full ks d = all (\k -> getName k `elem` ks) (tyConDataCons d)

runInferM ::
  InferM a ->
  Module ->
  M.Map Name Scheme ->
  (a, [Error])
runInferM run mod_name init_env =
  evalRWS run
    (InferEnv mod_name [] IM.empty init_env (UnhelpfulSpan (mkFastString "Top level")))
    (InferState 0 empty)

-- Transitively remove local constraints and attach them to variables
saturate :: Context -> InferM Context
saturate ts = do
  cg <- gets InferM.constraints
  let interface = domain ts
  pprTraceM "Constraints: " (ppr cg)
  case runExcept (Constraints.saturate interface cg) of
    Left e -> do
      tell [Error e]
      modify (\s -> s {InferM.constraints = empty})
      -- Continue ignoring the constraints from this recursive group
      return ((\s -> s {boundvs = IS.toList interface, Scheme.constraints = Nothing}) <$> ts)
    Right cg' -> do
      modify (\s -> s {InferM.constraints = empty})
      return ((\s -> s {boundvs = IS.toList interface, Scheme.constraints = Just cg'}) <$> ts)
