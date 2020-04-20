{-# LANGUAGE GADTs #-}

module InferM
  ( Flags (..),
    Context,
    InferM,
    runInferM,
    setLoc,
    topLevel,
    isBranchReachable,
    branch,
    putVar,
    putVars,
    fromCore,
    fromCoreScheme,
    fromCoreCons,
    fromCoreConsInst,
    getExternalName,
    emit,
    saturate,
  )
where

import ConGraph
import Constraints
import qualified Data.List as L
import InferM.Emit
import InferM.FromCore
import InferM.Internal
import Outputable
import Scheme
import Types

-- Transitively remove local constraints and attach them to variables
saturate :: Monad m => InferM m Context -> InferM m Context
saturate m = InferM $ \mod gamma occ_l path fresh cg -> do
  (path', fresh', cg', ts) <- unInferM m mod gamma occ_l path fresh cg
  let interface = freevs ts L.\\ freevs gamma
  case restrict interface cg' of
    Right cs ->
      return (path', fresh', cg, (\s -> s {boundvs = interface, constraints = Just cs}) <$> ts)
    Left (Con k left_l, Set k' right_l) ->
      pprPanic "Unsatisfiable constraint!" $ ppr (k, k', left_l, right_l, occ_l, gamma, cg')
