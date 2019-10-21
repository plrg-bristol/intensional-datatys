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
import qualified DataCon as D
import qualified CoreUtils as Utils

data CaseAlt = Default | Literal [Core.Literal] | DataCon [(Core.DataCon, [Type])] | Empty

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
      cg' <- insert (sub xs ys u) v cg
      cg'' <- foldM (\cg (x, se) -> substitute se cg x) cg' (zip xs ys)
      return $ (v, graphMap (subTypeVars as ts') cg'')

infer :: Core.Expr Core.Var -> InferM (Type, ConGraph)
infer (Core.Var x) =
  if isConstructor x
    then do
      -- Infer constructor
      (d, args) <- safeCon x
      ts <- mapM fresh args
      t  <- fresh $ SData d
      cg <- insert (K x ts) t empty
      return (foldr (:=>) t ts, cg)
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
        t3 :=> t4 -> do
          cg <- union c1 c2
          cg' <- insert t2 t3 cg
          return (t4, cg')

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
    cg'' <- union cg cg'
    return (t:ts, cg'')
    ) ([], empty) rhss

  -- Restrict constraints to vars with stems appearing in ts'
  let lcg' = graphFilter (interface ts') lcg

  -- Infer in body
  (t, icg) <- withBinds (infer e)

  cg <- union icg lcg'
  -- ts will only be of the form (Forall as [] empty) and ts' will be implicitly quantified over as
  cg' <- foldM (\cg (t', Forall as _ _ t) -> insert t' t cg) cg (zip ts' ts)
  return (t, cg')

infer (Core.Case e b t as) = do
  -- Infer case expession
  et <- fresh $ toSort $ Utils.exprType e
  t' <- fresh $ toSort t
  (t0, c0)   <- infer e
  (caseType, cg) <- local (insertVar b $ Forall [] [] empty et) $ foldM (\(caseType, cg) a ->
    case a of
      -- Infer constructor alternative
      (Core.DataAlt d, bs, rhs) -> do
        ts <- mapM (toFreshTypeScheme . Core.varType) bs
        let ts' = undefined -- getArgs of d
        cg' <- foldM (\cg (t', Forall as _ _ t) -> insert t' t cg) cg (zip ts' ts)
        (dt, cg'') <- local (insertMany bs ts) (infer rhs)
        cg''' <- insert dt t' cg''
        cg'''' <- cg' `union` cg'''
        case caseType of
          Empty     -> return (DataCon [(d, ts')], cg'''')
          Default   -> return (Default, cg'''')
          DataCon s -> return (DataCon ((d, ts'):s), cg'''')

      -- Infer literal alternative
      (Core.LitAlt l, [], rhs) -> do
        (dt, cg') <- infer rhs
        cg'' <- insert dt t' cg'
        cg''' <- cg `union` cg''
        case caseType of
          Default    -> return (Default, cg''')
          Literal s  -> return (Literal (l:s), cg''')
          Empty      -> return (Literal [l], cg''')

      -- Infer default alternative
      (Core.DEFAULT, [], rhs) -> do
        (dt, cg') <- infer rhs
        cg'' <- insert dt t' cg'
        cg''' <- cg `union` cg''
        return (Default, cg''')
    ) (Empty, c0) as

  -- Ensure destructor is total
  case caseType of
    Default -> return (t', cg)
    DataCon dts -> do
      cg' <- insert t0 (Sum [(TData dc, ts) | (dc, ts) <- dts]) cg
      return (t', cg)
    Literal lss -> error "Literal cases must contain defaults."


infer (Core.Tick _ e) = infer e

infer (Core.Type t) = error "Cannot infer RankN programs."

infer _ = error "Unimplemented"
