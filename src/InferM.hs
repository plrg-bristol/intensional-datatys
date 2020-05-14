{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}

module InferM
  ( InferM,
    runInferM,
    Context,
    putVar,
    putVars,
    getVar,
    freshRVar,
    branchGuard,
    topLevel,
    isBranchReachable,
    branch,
    congraph,
    unrollDataTypes,
    allowContra,
    genLet,
    modName,
    branchPath,
    varEnv,
    inferLoc,
    Error (..),
    saturate,
  )
where

import ConGraph
import Constraints
import Control.Lens hiding (Context)
import Control.Monad.Except hiding (guard)
import Control.Monad.RWS hiding (guard)
import Data.Bifunctor
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.IntMap as I
import qualified Data.HashMap.Lazy as H
import DataTypes
import GhcPlugins hiding (L, empty)
import Guards
import IfaceType
import Scheme
import ToIface
import qualified TyCoRep as Tcr
import Types

-- A Path records the terms that have been matched against in the current path
type Path = [(CoreExpr, [DataCon])]

intoBranch :: CoreExpr -> [DataCon] -> Path -> Path
intoBranch e ks = ((e, ks) :)

-- Check if an expression is in the path
topLevel :: CoreExpr -> Path -> Bool
topLevel e = foldr (\(e', _) es -> not (cheapEqExpr e e') && es) True

-- Check if a branch is possible, i.e. doesn't contradict the current branch
isBranchReachable :: CoreExpr -> DataCon -> Path -> Bool
isBranchReachable e k = foldr (\(e', ks) es -> (not (cheapEqExpr e e') || k `elem` ks) && es) True

-- The environment variables and their types
type IContext s = M.Map Name (Scheme IfaceTyCon (GuardSet s))

type Context s = M.Map Name (Scheme TyCon (GuardSet s))

instance (Monad m, Refined a m) => Refined (M.Map k a) m where
  domain m = foldM (\k -> fmap (L.union k) . domain) [] m
  rename x y = mapM (rename x y)

-- Insert variables into environment
putVar :: Name -> Scheme TyCon (GuardSet s) -> IContext s -> IContext s
putVar n = M.insert n . first toIfaceTyCon

putVars :: Context s -> IContext s -> IContext s
putVars = M.union . fmap (first toIfaceTyCon)

-- Lookup constrained variable
getVar :: Var -> IContext s -> Maybe (Scheme TyCon (GuardSet s))
getVar v = fmap (promoteSch vty_body) . M.lookup (getName v)
  where
    vty_body :: Tcr.Type
    vty_body = snd $ splitForAllTys $ varType v

data InferState s = InferState
  { _freshRVar :: RVar,
    _branchGuard :: GuardSet s,
    _congraph :: ConGraph s,
    _memo' :: M.Map Memo (GuardSet s),
    _freshId' :: ID,
    _nodes' :: I.IntMap (Node s),
    _hashes' :: H.HashMap (Node s) ID
  }

makeLenses ''InferState

instance GuardState (InferState s) s where
  memo = memo'
  freshId = freshId'
  nodes = nodes'
  hashes = hashes'

-- Provides meta-data and a context for inference
data InferEnv s = InferEnv
  { _unrollDataTypes :: Bool,
    _allowContra :: Bool,
    _genLet :: Bool,
    _modName :: Module,
    _branchPath :: Path, -- The path records which terms have been matched against
    _varEnv :: IContext s,
    _inferLoc :: SrcSpan
  }

makeLenses ''InferEnv

-- The inference monad
type InferM s m = ExceptT Error (RWST (InferEnv s) () (InferState s) m)

-- Locally guard constraints
branch :: Monad m => CoreExpr -> [DataCon] -> RVar -> DataType TyCon -> InferM s m a -> InferM s m a
branch e ks x d m = do
  old <- use branchGuard
  g <- dom (getName <$> ks) x (getName <$> d)
  branchGuard <~ g &&& old
  r <- locally branchPath (intoBranch e ks) m
  branchGuard .= old -- restore old guard
  return r

data Error = forall l r.
  Error
  { dty :: DataType Name,
    lhs :: K l,
    rhs :: K r,
    errorLoc :: SrcSpan
  }

instance Outputable Error where
  ppr (Error dty lhs rhs errorLoc) = ppr (dty, lhs, getConstraintLoc lhs, rhs, getConstraintLoc lhs, errorLoc)

runInferM :: Monad m => (forall s. InferM s m a) -> Bool -> Bool -> Bool -> Module -> M.Map Name (Scheme IfaceTyCon [[Guard]]) -> m (Either Error a)
runInferM run ur ac gl mn env =
  fst
    <$> evalRWST
      ( runExceptT $ do
          env' <- mapM (mapM fromList) env
          locally varEnv (const env') run
      )
      (InferEnv ur ac gl mn [] M.empty $ UnhelpfulSpan (mkFastString "Top level"))
      (InferState 0 Top empty M.empty 0 I.empty H.empty)

-- Transitively remove local constraints and attach them to variables
saturate :: Monad m => InferM s m (Context s) -> InferM s m (Context s)
saturate m = do
  old_cg <- use congraph

  ts <- m
  cg <- use congraph

  l <- view genLet
  gamma <- view varEnv
  interface <- if l then liftM2 (L.\\) (domain ts) (domain gamma) else domain ts

  loc <- view inferLoc
  cg' <- withExceptT (\(d, l, r) -> Error d l r loc) $ restrict interface cg

  -- Restore old state
  congraph .= old_cg
  return ((\s -> s {boundvs = interface, constraints = Just cg'}) <$> ts)
