module InferM
  ( InferM,
    Context,
    InferEnv (..),
    InferState (constraints),
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
import qualified Data.IntSet as I
import qualified Data.Map as M
import GhcPlugins hiding ((<>), singleton)
import Scheme
import Types

type InferM = RWS InferEnv [Atomic] InferState

type Path = [(CoreExpr, DataCon)]

type Context = M.Map Name Scheme

data InferEnv
  = InferEnv
      { modName :: Module, -- The current module
        branchPath :: Path, -- Expressions which have been match upon
        branchGuard :: Guard,
        varEnv :: Context,
        inferLoc :: SrcSpan -- The current location in the source text
      }

data InferState
  = InferState
      { next :: RVar,
        constraints :: ConstraintSet
      }

runInferM ::
  InferM a ->
  Module ->
  Context ->
  (a, [Atomic])
runInferM run mod_name init_env =
  evalRWS
    run
    (InferEnv mod_name [] mempty init_env (UnhelpfulSpan (mkFastString "Top level")))
    (InferState 0 mempty)

-- Transitively remove local constraints and attach them to variables
saturate :: Context -> InferM Context
saturate ts = do
  let interface = foldMap domain ts
  cg <- gets InferM.constraints
  let intermediate = I.difference (domain cg) interface
  -- Reset constraints
  modify (\s -> s {InferM.constraints = mempty})
  return
    ( ( \s ->
          s -- Add constraints to every type in the recursive group
            { boundvs = I.toList interface,
              Scheme.constraints = Constraints.saturate intermediate cg
            }
      )
        <$> ts
    )

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
  modify
    ( \s ->
        s
          { InferM.constraints =
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
                (InferM.constraints s)
                (toAtomic k1 k2)
          }
    )

-- A fresh refinement variable
fresh :: InferM RVar
fresh = do
  s@InferState {next = i} <- get
  put s {next = i + 1}
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
