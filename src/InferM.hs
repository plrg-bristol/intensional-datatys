{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module InferM
  ( Flags (..),
    Error (..),
    Context,
    InferM,
    runInferM,
    setLoc,
    topLevel,
    defaultLevel,
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
import qualified Data.Set as S
import qualified Data.List as L
import InferM.Emit
import InferM.FromCore
import InferM.Internal
import Outputable
import Scheme
import Types

-- Transitively remove local constraints and attach them to variables
saturate :: Monad m => InferM m Context -> InferM m Context
saturate m = InferM $ \flags gamma occ_l path fresh old_fresh cg ->
  unInferM m flags gamma occ_l path fresh old_fresh cg >>= \case
    Left err -> return $ Left err
    Right (path', fresh', old_fresh', cg', ts) -> do
      let domain = S.fromList [old_fresh' .. (fresh' - 1)]
      let interface = if False {- gen elt -} then freevs ts L.\\ freevs gamma else freevs ts
      case restrict interface domain cg' of
        Right cs ->
          return $ Right (path', fresh', fresh, cg, (\s -> s {boundvs = interface, constraints = Just cs}) <$> ts)
        Left (d, k1, k2) ->
          return $ Left (Error "Unsatisfiable constraint!" occ_l d k1 k2)
