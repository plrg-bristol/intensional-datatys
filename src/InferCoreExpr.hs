module InferCoreExpr
    (
    ) where

import InferM
import GenericConGraph
import Control.Monad.RWS hiding (Sum)
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
  return (id, toSort t:ts)
fromPolyVar _ = Nothing

-- Restrict the constraints of a typescheme to refinement variable that have the same stem as a refinement variable that apepars in the scheme's body
inferface :: TypeScheme -> TypeScheme
inferface = undefined

-- Infer fully instantiated polymorphic variable
inferVar :: Core.Var -> [Sort] -> InferM (Type, ConGraph)
inferVar x ts = do
  (Forall as xs cg u) <- safeVar x
  if length as /= length ts
    then throwError $ PolyTypeError
    else do
      ys  <- mapM fresh $ map (\(RVar x p d) -> SData d) xs
      ts' <- mapM fresh ts
      let m = M.fromList (zip xs ys)      -- booo we don't like fromList
      v   <- fresh $ toSort $ Core.varType x
      case do
          cg' <- insert (sub m u) v cg
          cg'' <- foldM (\cg (x, se) -> substitute se cg x) cg' (M.toList m)
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
      case insert (mkCon x ts) t empty of
        Just cg   -> return (mkConArgs ts t, cg)
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
      let (t3, t4) = desugarArrow t1
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
  return (mkArrow t1 t2, cg)

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

  -- Restrict lcg to vars with stems appearing in ts'

  -- Infer in body
  (t, icg) <- withBinds (infer e)

  case do
    cg' <- union icg lcg
    -- ts will only be of the form (Forall as [] empty) and ts' will be implicitly quantified over as
    foldM (\cg (t', Forall as _ _ t) -> insert t' t cg) cg' (zip ts' ts)
    of
      Just cg   -> return (t, cg)
      otherwise -> throwError ConstraintError
