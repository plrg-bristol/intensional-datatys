{-# LANGUAGE FlexibleInstances #-}

module InferM
  ( InferM,
    Context,
    InferEnv (..),
    runInferM,
    InferM.saturate,
    topLevel,
    isBranchReachable,
    branch,
    branchWithExpr,
    branchAny,
    emit,
    fresh,
    putVar,
    putVars,
    setLoc,
    getExternalName,
  )
where

import Constraints
import Constructors
import Control.Monad.RWS hiding (guard)
import qualified Data.Map as M
import GhcPlugins hiding ((<>), singleton)
import Scheme
import Types

type InferM = RWS InferEnv ConstraintSet RVar

type Path = [(CoreExpr, DataCon)]

type Context = M.Map Name Scheme

instance Refined Context where
  domain = foldMap domain
  rename x y = fmap (rename x y)

data InferEnv
  = InferEnv
      { modName :: Module, -- The current module
        branchPath :: Path, -- Expressions which have been match upon
        branchGuard :: Guard,
        varEnv :: Context,
        inferLoc :: SrcSpan -- The current location in the source text
      }

runInferM ::
  InferM a ->
  Module ->
  Context ->
  a
runInferM run mod_name init_env =
  fst $
    evalRWS
      run
      (InferEnv mod_name [] mempty init_env (UnhelpfulSpan (mkFastString "Top level")))
      0

-- Transitively remove local constraints
saturate :: Refined a => InferM a -> InferM a
saturate ma = pass $ do
  a <- ma
  env <- asks varEnv
  g <- asks branchGuard
  let interface = domain a <> domain env <> domain g
  return (a, Constraints.saturate interface)

-- Check if an expression has already been pattern matched
topLevel :: CoreExpr -> InferM Bool
topLevel e = asks (foldr (\(e', _) es -> not (cheapEqExpr e e') && es) True . branchPath)

-- Check that a branch doesn't contradict the current branch
isBranchReachable :: CoreExpr -> DataCon -> InferM Bool
isBranchReachable e k =
  asks
    ( foldr
        ( \(e', k') es ->
            (not (cheapEqExpr e e') || k == k') && es
        )
        True
        . branchPath
    )

-- Locally guard constraints
branch :: DataCon -> DataType TyCon -> InferM a -> InferM a
branch k d =
  local
    ( \env ->
        env
          { branchGuard = singleton (getName k) (fmap getName d) <> branchGuard env
          }
    )

-- Locally guard constraints and add expression to path
branchWithExpr :: CoreExpr -> DataCon -> DataType TyCon -> InferM a -> InferM a
branchWithExpr e k d =
  local
    ( \env ->
        env {branchPath = (e, k) : branchPath env}
    )
    . branch k d

-- Locally guard constraints and add expression to path
branchAny :: CoreExpr -> [DataCon] -> DataType TyCon -> InferM a -> InferM ()
branchAny e ks d m = mapM_ (\k -> branchWithExpr e k d m) ks

-- Emit a (non-)atomic constriant with the current branch guard
emit :: K l -> K r -> InferM ()
emit k1 k2 = do
  l <- asks inferLoc
  g <- asks branchGuard
  tell
    ( foldMap
        ( \(k1', k2') ->
            insert
              ( Constraint
                  { left = k1',
                    right = k2',
                    guard = g,
                    Constraints.srcSpan = l
                  }
              )
              mempty
        )
        (toAtomic k1 k2)
    )

-- A fresh refinement variable
fresh :: InferM RVar
fresh = do
  i <- get
  put (i + 1)
  return i

-- Insert variables into environment
putVar :: Name -> Scheme -> InferM a -> InferM a
putVar n s = local (\env -> env {varEnv = M.insert n s (varEnv env)})

putVars :: Context -> InferM a -> InferM a
putVars ctx = local (\env -> env {varEnv = M.union ctx (varEnv env)})

-- Add source text location tick
setLoc :: RealSrcSpan -> InferM a -> InferM a
setLoc l = local (\env -> env {inferLoc = RealSrcSpan l})

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: NamedThing a => a -> InferM Name
getExternalName a = do
  let n = getName a
  mn <- asks modName
  return $ mkExternalName (nameUnique n) mn (nameOccName n) (nameSrcSpan n)
