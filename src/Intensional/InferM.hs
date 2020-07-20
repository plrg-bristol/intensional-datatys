{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- The Refined Instance for Context is an orphan

module Intensional.InferM
  ( InferM,
    Context,
    InferEnv (..),
    Stats (..),
    runInferM,
    Intensional.InferM.saturate,
    topLevel,
    isBranchReachable,
    branch,
    branchWithExpr,
    branchAny,
    emitDD,
    emitDK,
    emitKD,
    fresh,
    putVar,
    putVars,
    setLoc,
    getExternalName,
    isTrivial,
    isIneligible,
    noteD,
    noteK,
    incrN,
    noteErrs,
  )
where

import Intensional.Constraints as Constraints
import Intensional.Constructors
import Control.Monad.RWS hiding (guard)
import qualified Data.IntSet as IntSet
import qualified Data.Map as M
import GhcPlugins hiding ((<>), singleton)
import Intensional.Scheme
import Intensional.Types
import Intensional.Ubiq
import Intensional.Guard

type InferM = RWS InferEnv ConstraintSet InferState

type Path = [(CoreExpr, DataCon)]

type Context = M.Map Name Scheme

instance Refined Context where
  domain = foldMap domain
  rename x y = fmap (rename x y)
  prpr m = foldr (($$) . prpr m) empty

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
          rVar :: Int,
          errs :: ConstraintSet
        }

initState :: InferState
initState = InferState 0 0 0 0 0 mempty

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

{-|
  Given a set of trivially unsatisfiable constraints @es@,
  @noteErrs es@ is the action that records them
  in the accumulating set in the inference state.
-}
noteErrs :: ConstraintSet -> InferM ()
noteErrs es = modify (\s -> s { errs = es <> errs s })

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
  (a, [Atomic], Stats)
runInferM run mod_name init_env =
  let (a, s, _) = runRWS run (InferEnv mod_name [] mempty init_env (UnhelpfulSpan (mkFastString "Nowhere"))) initState
  in (a, Constraints.toList (errs s), Stats (maxK s) (maxD s) (rVar s) (maxI s) (cntN s))

-- Transitively remove local constraints
saturate :: Refined a => InferM a -> InferM a
saturate ma = pass $
  do
    a <- ma
    env <- asks varEnv
    m <- asks modName
    g <- asks branchGuard
    src <- asks inferLoc
    let interface = domain a <> domain env <> domain g
    noteI (IntSet.size interface)
    let fn cs =
          let csSize = size cs
              ds = Constraints.saturate (CInfo m src) interface cs
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

-- Check if a core datatype is ineligible for refinement
isIneligible :: TyCon -> InferM Bool
isIneligible tc =  
  do  m <- asks modName
      return (not (homeOrBase m (getName tc)) || null (tyConDataCons tc))
  where
    strName = occNameString (getOccName tc)
    homeOrBase m n =
      nameIsHomePackage m n 
      || strName == "Bool"
      || strName == "Maybe"
        -- Previously we tried to include as much of base as possible by asking for specific modules
        -- but this is a little too coarse grain (e.g. GHC.Types will include Bool, but also Int):
        --
        -- vc|| ( not (nameIsFromExternalPackage baseUnitId n && nameIsFromExternalPackage primUnitId n)
        --        && case nameModule_maybe n of
        --          Nothing -> False
        --          Just (Module _ m) ->
        --            List.isPrefixOf "Prelude" (moduleNameString m)
        --              || List.isPrefixOf "Data" (moduleNameString m)
        --              || List.isPrefixOf "GHC.Base" (moduleNameString m)
        --              || List.isPrefixOf "GHC.Types" (moduleNameString m)
        --    )

isTrivial :: TyCon -> Bool
isTrivial tc = (== 1) (length (tyConDataCons tc))


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
branch _ (Base _)  ma = ma
branch k (Inj x d) ma =
    -- If the datatype has only 1 constructor, there is no point
    if isTrivial d then ma else local envUpdate ma
  where
    dn = getName d
    kn = getName k
    envUpdate env =
      env {branchGuard = singleton [kn] x dn <> branchGuard env}

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

mkConFromCtx :: ConL -> ConR -> InferM Atomic
mkConFromCtx l r =
  do  m <- asks modName
      s <- asks inferLoc
      g <- asks branchGuard
      return (Constraint l r g (CInfo m s))

emitDD :: DataType TyCon -> DataType TyCon -> InferM ()
emitDD (Inj x d) (Inj y _) = 
  unless (isTrivial d) $ 
    do  a <- mkConFromCtx (Dom (Inj x dn)) (Dom (Inj y dn))
        tell (Constraints.fromList [a])
  where
    dn = getName d
emitDD _ _ = return ()

emitKD :: DataCon -> SrcSpan -> DataType TyCon -> InferM ()
emitKD k s (Inj x d) =
  unless (isTrivial d) $ 
    do  a <- mkConFromCtx (Con kn s) (Dom (Inj x dn))
        tell (Constraints.fromList [a])
  where
    dn  = getName d
    kn = getName k
emitKD _ _ _ = return ()

emitDK :: DataType TyCon -> [DataCon] -> SrcSpan -> InferM ()
emitDK (Inj x d) ks s =
  unless (isTrivial d) $ 
    do  a <- mkConFromCtx (Dom (Inj x dn)) (Set ksn s)
        tell (Constraints.fromList [a])
  where
    dn  = getName d
    ksn = mkUniqSet (map getName ks)
emitDK _ _ _ = return ()


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