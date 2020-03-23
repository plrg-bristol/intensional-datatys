{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module InferCoreExpr (
  inferProg
) where

import Control.Monad
import qualified Data.Map as M

import Types
import Scheme
import Guard
import ConGraph
import InferM

import Name
import SrcLoc hiding (getLoc)
import TyCon
import CoreUtils
import Outputable hiding (empty)
import qualified GhcPlugins as Core

-- Infer recursive bind
inferRec :: Monad m => Core.CoreBind -> InferM m (Context ConGraph)
inferRec bgs = do
  binds <- sequence $ M.fromList [ (n, fromCoreScheme (exprType rhs))
                                 | (x, rhs) <- Core.flattenBinds [bgs],
                                   let n    =  getName x ]

  -- Restrict type schemes
  saturate $
    -- Add binds for recursive calls
    putVars binds $
                             -- Infer rhs; subtype of recursive usage
      sequence $ M.fromList [ (n, infer rhs >>= \s -> s <$ emitTyCon (body s) (body sr))
                            | (x, rhs) <- Core.flattenBinds [bgs],
                              let n    = getName x,
                              let sr   = binds M.! n ]
-- Infer program
inferProg :: Monad m => Core.CoreProgram -> InferM m (Context ConGraph)
inferProg = foldM (\ctx -> fmap (M.union ctx) . putVars ctx . inferRec) M.empty

infer :: Monad m => Core.CoreExpr -> InferM m (Scheme T TyCon ())
infer (Core.Var v) =
  case Core.isDataConId_maybe v of
    Just k
        -- Ignore typeclass evidence
      | Core.isClassTyCon $ Core.dataConTyCon k -> return $ Mono Ambiguous

        -- Infer constructor
      | otherwise -> do
        scheme <- fromCoreScheme $ Core.varType v
        case decomp (body scheme) of
          -- Refinable datatype
          (args, Inj x d _) -> do
            emitConDom k x d
            mapM_ (\t -> emitTyCon t (inj x t)) args

          -- Unrefinedable
          _ -> return ()

        return scheme

    -- Infer variable
    Nothing -> getVar v

-- Type literal
infer l@(Core.Lit _) = fromCoreScheme $ Core.exprType l

-- Type application
infer (Core.App e1 (Core.Type e2)) = do
  t <- fromCore e2
  scheme <- infer e1
  when (isConstructor e1) $
    case decomp (body scheme) of
      (_, Inj x d _) -> emitTyCon t (inj x t)
      _              -> return ()

  return (applyType scheme t)
  where
    isConstructor :: Core.CoreExpr -> Bool
    isConstructor (Core.App e1 _) = isConstructor e1
    isConstructor (Core.Var v) =
      case Core.isDataConId_maybe v of
        Just k  -> not (Core.isClassTyCon $ Core.dataConTyCon k)
        Nothing -> False

-- Term application
infer (Core.App e1 e2) = infer e1 >>= \case
  Forall as Ambiguous -> Forall as Ambiguous <$ infer e2

  -- This should raise a warning for as /= []!
  Forall as (t3 :=> t4) -> do
    t2 <- mono <$> infer e2
    emitTyCon t2 t3
    return $ Forall as t4

  _ -> pprPanic "Term application to non-function!" $ ppr (Core.exprType e1, Core.exprType e2)

infer (Core.Lam x e)
  | Core.isTyVar x = do
    -- Type abstraction
    a <- getExternalName x
    infer e >>= \case
      Forall as t -> return $ Forall (a:as) t

  | otherwise = do
    -- Variable abstraction
    t1 <- fromCore $ Core.varType x
    putVar (getName x) (Mono t1) (infer e) >>= \case
      Forall as t2 -> return $ Forall as (t1 :=> t2)

-- Local prog
infer (Core.Let b e) = do
  ts <- inferRec b
  putVars ts $ infer e

infer (Core.Case e bind_e core_ret alts) = do
  -- Fresh return type
  ret <- fromCore core_ret

  -- Separate default case
  let altf = filter (\(_, _, rhs) -> not $ Core.exprIsBottom rhs) alts
  let (alts', def) = Core.findDefault altf

  -- Infer expression on which to pattern match
  t0 <- mono <$> infer e

  -- Add the variable under scrutinee to scope
  putVar (getName bind_e) (Mono t0) $ case t0 of

    -- Infer a refinable case expression
    Inj rvar d _ -> do
      ks <- traverse (\(Core.DataAlt k, xs, rhs) -> do
          -- Add constructor arguments introduced by the pattern
          ts <- sequence $ M.fromList [ (n, Mono <$> fromCore (Core.varType x))
                                      | x     <- xs,
                                        let n =  getName x ]

          branch e [k] rvar d $ do
            -- Constructor arguments are from the same refinement environment
            mapM_ (\(Mono kti) -> emitTyCon (inj rvar kti) kti) ts

            -- Ensure return type is valid
            ret_i <- mono <$> putVars ts (infer rhs)
            emitTyCon ret_i ret

          -- Record constructors
          return k
        ) alts'

      case def of
        Nothing -> do
          -- Ensure destructor is total if not nested
          top <- topLevel e
          when top $ emitDomSet rvar d ks
        Just rhs ->
          -- Guard default case by constructors that have not occured
          branch e ks rvar d $ do
            ret_i <- mono <$> infer rhs
            emitTyCon ret_i ret

    -- Infer an unrefinable case expression
    _ ->
      mapM_ (\(_, xs, rhs) -> do
        -- Add constructor arguments introduced by the pattern
        ts <- sequence $ M.fromList [ (n, Mono <$> fromCore (Core.varType x))
                                    | x     <- xs,
                                      let n =  getName x ]

        -- Ensure return type is valid
        ret_i <- mono <$> putVars ts (infer rhs)
        emitTyCon ret_i ret
      ) altf

  return $ Mono ret

-- Track source location
infer (Core.Tick t e) = setLoc (RealSrcSpan $ Core.sourceSpan t) $ infer e

-- Infer cast
infer (Core.Cast e _) = do
  infer e
  return (Mono Ambiguous)

-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"
