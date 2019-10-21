module InferCoreExpr
    (
    ) where

import InferM
import GenericConGraph
import Control.Monad.RWS
import Control.Monad.Except
import qualified Data.Map as M
import qualified GhcPlugins as Core
import qualified CoreUtils as Utils

isConstructor :: Core.Id -> Bool
isConstructor = undefined

fromPolyVar :: Core.CoreExpr -> Maybe (Core.Id, [Sort])
fromPolyVar (Core.Var i) = Just (i, [])
fromPolyVar (Core.App e1 (Core.Type t)) = do
  (id, ts) <- fromPolyVar e1
  return (id, fromCoreType t:ts)
fromPolyVar _ = Nothing

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer (Core.Var x) =
  if isConstructor x
    then do
      -- Infer constructor
      (d, args) <- safeCon x
      ts <- mapM fresh args
      t  <- fresh $ SData d
      case insert (mkCon x ts) t empty of
        Just cg   -> return (mkConArgs ts t, cg)
        otherwise -> throwError ConstraintError

    else do
      -- Infer monomorphic variable
      (Forall as xs cg u) <- safeVar x
      if length as == 0
        then do
          ys <- mapM fresh $ map (\(RVar x p d) -> SData d) xs
          let m = M.fromList (zip xs ys)
          v  <- fresh $ fromCoreType $ Core.varType x
          case do
              cg' <- insert (sub m u) v cg
              foldM (\cg (x, se) -> substitute se cg x) cg' (M.toList m)
            of
            Just cg'' -> return (v, cg'')
            otherwise -> throwError ConstraintError
        else
          throwError $ PolyTypeError

infer l@(Core.Lit _) = do
  -- Infer literal expression
  t' <- fresh $ fromCoreType $ Utils.exprType l
  return (t', empty)

infer e@(Core.App e1 e2) =
  case fromPolyVar e of
    Just (x, ts) -> do
      -- Infer polymorphic variable
      (Forall as xs cg u) <- safeVar x
      if length as /= length ts
        then throwError $ PolyTypeError
        else do
          ys <- mapM fresh $ map (\(RVar x p d) -> SData d) xs
          ts' <- mapM fresh ts
          let m = M.fromList (zip xs ys)
          v  <- fresh $ fromCoreType $ Core.varType x
          case do
              cg' <- insert (sub m u) v cg
              cg'' <- foldM (\cg (x, se) -> substitute se cg x) cg' (M.toList m)
              return $ fmap (subTypeVars as ts') cg''
            of
            Just cg'' -> return (v, cg'')
            otherwise -> throwError ConstraintError

    otherwise -> do
      -- Infer application
      (t1, c1) <- infer e1
      (t2, c2) <- infer e2
      case t1 of
        Con TArrow [t3, t4] ->
          case do
              cg <- union c1 c2
              cg' <- insert t2 t3 cg
              return (t4, cg')
            of
              Just r -> return r
              otherwise -> throwError ConstraintError
        otherwise -> throwError ApplicationError

-- infer (Core.Lam b e) = do
  -- Infer abstraction
