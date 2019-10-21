module InferCoreExpr
    (
    ) where

import Utils
import GenericConGraph
import Control.Monad.RWS hiding (Sum)
import Data.List hiding (filter, union, insert)
import Control.Monad.Except
import qualified Data.Map as M
import qualified GhcPlugins as Core
import qualified CoreUtils as Utils

-- Infer fully instantiated polymorphic variable
inferVar :: Core.Var -> [Sort] -> InferM (Type, ConGraph)
inferVar x ts = do
  (Forall as xs cg u) <- safeVar x
  if length as /= length ts
    then throwError $ PolyTypeError
    else do
      ys  <- mapM fresh $ map (\(RVar (x, p, d)) -> SData d) xs
      ts' <- mapM fresh ts
      v   <- fresh $ toSort $ Core.varType x
      case do
          cg' <- insert (sub xs ys u) v cg
          cg'' <- foldM (\cg (x, se) -> substitute se cg x) cg' (zip xs ys)
          graphMap (subTypeVars as ts') cg''
        of
        Just cg'' -> return (v, cg'')
        otherwise -> throwError ConstraintError

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer (Core.Var x) =
  if isConstructor x
    then do
      -- Infer constructor
      (d, args) <- safeCon x
      ts <- mapM fresh args
      t  <- fresh $ SData d
      case insert (K x ts) t empty of
        Just cg   -> return (foldr (:=>) t ts, cg)
        otherwise -> throwError ConstraintError
    else
      -- Infer monomorphic variable
      inferVar x []

infer l@(Core.Lit _) = do
  -- Infer literal expression
  t' <- fresh $ toSort $ Utils.exprType l
  return (t', empty)

infer e@(Core.App e1 e2) =
  case fromPolyVar e of
    Just (x, ts) -> do
      -- Infer polymorphic variable
      inferVar x ts
    otherwise -> do
      -- Infer application
      (t1, c1) <- infer e1
      (t2, c2) <- infer e2
      case t1 of
        t3 :=> t4 ->
          case do
              cg <- union c1 c2
              cg' <- insert t2 t3 cg
              return (t4, cg')
            of
              Just r -> return r
              otherwise -> throwError ConstraintError

infer (Core.Lam x e) = do
  -- Infer abstraction
  t1 <- fresh $ toSort $ Core.varType x
  (t2, cg) <- local (insertVar x $ Forall [] [] empty t1) (infer e)
  return (t1 :=> t2, cg)

infer (Core.Let b e) = do
  -- Infer local module (i.e. let expression)
  let xs = Core.bindersOf b
  let rhss = Core.rhssOfBind b
  ts <- mapM (toFreshTypeScheme . Core.varType) xs
  let withBinds = local (insertMany xs ts)

  -- Infer rhs of binders
  (ts', lcg) <- foldM (\(ts, cg) rhs -> do
    (t, cg') <- withBinds (infer rhs)
    case union cg cg' of
      Just cg'' -> return (t:ts, cg'')
      otherwise -> throwError ConstraintError) ([], empty) rhss

  -- Restrict constraints to vars with stems appearing in ts'
  let lcg' = graphFilter (interface ts') lcg

  -- Infer in body
  (t, icg) <- withBinds (infer e)

  case do
    cg' <- union icg lcg'
    -- ts will only be of the form (Forall as [] empty) and ts' will be implicitly quantified over as
    foldM (\cg (t', Forall as _ _ t) -> insert t' t cg) cg' (zip ts' ts)
    of
      Just cg   -> return (t, cg)
      otherwise -> throwError ConstraintError

infer (Core.Case e b t as) = do
  et <- fresh $ toSort $ Utils.exprType e
  t' <- fresh $ toSort t
  (t0, c0) <- infer e
  cg' <- local (insertVar b $ Forall [] [] empty et) $ foldM (\cg a ->
    case a of
      -- These will need some accumualtors as well
      (Core.DataAlt d, bs, rhs) -> error ""
      (Core.LitAlt l, bs, rhs) -> error ""
      (Core.DEFAULT, bs, rhs) -> error ""
    ) c0 as
  return (t', cg')

infer (Core.Tick _ e) = infer e

infer (Core.Type t) = error "Cannot infer RankN programs."

infer _ = error "Unimplemented"
