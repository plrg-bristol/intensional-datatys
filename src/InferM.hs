{-# LANGUAGE FlexibleInstances #-}

module InferM
  ( InferM,
    Context,
    InferEnv (..),
    Stats (..),
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
    trivial,
    noteD,
    noteK,
    incrN
  )
where

import Constraints
import Constructors
import Control.Monad.RWS hiding (guard)
import qualified Data.IntSet as IntSet
import qualified Data.List as List
import qualified Data.Map as M
import GhcPlugins hiding ((<>), singleton)
import Scheme
import Types
import Ubiq

type InferM = RWS InferEnv ConstraintSet InferState

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

data InferState = 
        InferState {
          maxK :: Int,
          maxD :: Int,
          maxI :: Int,
          cntN :: Int,
          rVar :: Int
        }

initState :: InferState
initState = InferState 0 0 0 0 0

noteK :: Int -> InferM ()
noteK x = modify (\s -> s { maxK = max x (maxK s) })

noteD :: Int -> InferM ()
noteD x = modify (\s -> s { maxD = max x (maxD s) })

noteI :: Int -> InferM ()
noteI x = modify (\s -> s { maxI = max x (maxI s) })

incrV :: InferM ()
incrV = modify (\s -> s { rVar = rVar s + 1 })

incrN :: InferM ()
incrN = modify (\s -> s { cntN = cntN s + 1 })

data Stats = 
        Stats {
          getK :: Int,
          getD :: Int,
          getV :: Int,
          getI :: Int,
          getN :: Int
        }

runInferM ::
  InferM a ->
  Module ->
  Context ->
  (a, Stats)
runInferM run mod_name init_env =
  let (a, s, _) = runRWS run (InferEnv mod_name [] mempty init_env (UnhelpfulSpan (mkFastString "Nowhere"))) initState
  in (a, Stats (maxK s) (maxD s) (rVar s) (maxI s) (cntN s))

-- Transitively remove local constraints
saturate :: Refined a => InferM a -> InferM a
saturate ma = pass $
  do
    a <- ma
    env <- asks varEnv
    g <- asks branchGuard
    src <- asks inferLoc -- this is actually only for debugging
    let interface = domain a <> domain env <> domain g
    noteI (IntSet.size interface)
    let fn cs =
          let csSize = size cs
              ds = Constraints.saturate interface cs
           in if debugging && csSize > 100 then debugBracket a env g src cs ds else ds
    return (a, fn)
  where
    debugBracket a env g src cs ds =
      let asz = "type: " ++ show (IntSet.size $ domain a)
          esz = "env: " ++ show (IntSet.size $ domain env)
          gsz = "guard: " ++ show (IntSet.size $ domain g)
          csz = show (size cs)
          spn = traceSpan src
          tmsg = "#interface = (" ++ asz ++ " + " ++ esz ++ " + " ++ gsz ++ "), #constraints = " ++ csz
          ds' = trace ("[TRACE] BEGIN saturate at " ++ spn ++ ": " ++ tmsg) ds
       in ds' `seq` trace ("[TRACE] END saturate at " ++ spn ++ " saturated size: " ++ (show $ size ds)) ds

-- Check if a core datatype has only one constructor or is otherwise ineligible
trivial :: TyCon -> InferM Bool
trivial tc =
  do
    m <- asks modName
    return (not (homeOrBase m (getName tc)) || (<= 1) (length (tyConDataCons tc)))
  where
    homeOrBase m n =
      nameIsHomePackage m n
        || ( nameIsFromExternalPackage baseUnitId n
               && case nameModule_maybe n of
                 Nothing -> False
                 Just (Module _ m) ->
                   List.isPrefixOf "Prelude" (moduleNameString m)
                     || List.isPrefixOf "Data" (moduleNameString m)
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
branch k d ma =
  do
    b <- trivial (tyconOf d)
    -- If the datatype has only 1 constructor, there is no point
    if b then ma else local envUpdate ma
  where
    envUpdate env =
      env {branchGuard = singleton (getName k) (fmap getName d) <> branchGuard env}

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
  i <- gets rVar
  incrV
  return i

-- Insert variables into environment
putVar :: Name -> Scheme -> InferM a -> InferM a
putVar n s = local (\env -> env {varEnv = M.insert n s (varEnv env)})

putVars :: Context -> InferM a -> InferM a
putVars ctx = local (\env -> env {varEnv = M.union ctx (varEnv env)})

-- Add source text location tick
setLoc :: SrcSpan -> InferM a -> InferM a
setLoc l = local (\env -> env {inferLoc = l})

-- Prepare name for interface
-- Should be used before all type variables
getExternalName :: NamedThing a => a -> InferM Name
getExternalName a = do
  let n = getName a
  mn <- asks modName
  return $ mkExternalName (nameUnique n) mn (nameOccName n) (nameSrcSpan n)