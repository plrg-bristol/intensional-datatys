{-# LANGUAGE GADTs #-}

module InferM (
  Context,
  InferM,
  runInferM,
  setLoc,
  topLevel,
  branch,
  putVar,
  putVars,

  fromCore,
  fromCoreScheme,
  getExternalName,

  emit,

  saturate,
) where

import qualified Data.List as L

import Outputable

import Emit
import Types
import Scheme
import ConGraph
import FromCore
import Constraints
import InferM.Internal

-- Transitively remove local constraints and attach them to variables
saturate :: Monad m => InferM m Context -> InferM m Context
saturate m = InferM $ \mod gamma occ_l path fresh cg -> do
  (path', fresh', cg', ts) <- unInferM m mod gamma occ_l path fresh cg
  let interface = freevs ts L.\\ freevs gamma
  case restrict interface cg' of
    Right cs ->
      return (path', fresh', cg, (\s -> s{ boundvs = interface, constraints = Just cs }) <$> ts)
    Left (Con k left_l, Set k' right_l) ->
      pprPanic "Unsatisfiable constraint!" $ ppr (k, k', left_l, right_l, occ_l, gamma, cg')

