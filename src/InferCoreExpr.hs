{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module InferCoreExpr (
  inferProg
) where

import Prelude hiding (sum)
import Control.Monad
import qualified Data.List as L
import qualified Data.Map as M

import Types
import Scheme
import Constraints
import ConGraph
import InferM

import Name
import SrcLoc hiding (getLoc)
import TyCon
import CoreUtils
import Outputable hiding (empty)
import qualified GhcPlugins as Core

-- Infer recursive bind
inferRec :: Monad m => Core.CoreBind -> InferM m Context
inferRec bgs = do
  binds <- sequence $ M.fromList [ (n, fromCoreScheme [] (exprType rhs))
                                 | (x, rhs) <- Core.flattenBinds [bgs],
                                   let n    =  getName x ]

  -- Restrict type schemes
  saturate $
    -- Add binds for recursive calls
    putVars binds $
                             -- Infer rhs; subtype of recursive usage
      sequence $ M.fromList [ (n, do { scheme <- infer [] rhs; emit (body scheme) (body sr); return scheme } )
                            | (x, rhs) <- Core.flattenBinds [bgs],
                              let n    = getName x,
                              let sr   = binds M.! n ]

-- Infer program
inferProg :: Monad m => Core.CoreProgram -> InferM m Context
inferProg = foldM (\ctx -> fmap (M.union ctx) . putVars ctx . inferRec) M.empty

isConstructor :: Core.CoreExpr -> Bool
isConstructor (Core.App e1 _) = isConstructor e1
isConstructor (Core.Var v) =
  case Core.isDataConId_maybe v of
    Just k  -> not (Core.isClassTyCon $ Core.dataConTyCon k)
    Nothing -> False
isConstructor _ = False


infer :: Monad m => [TyCon] -> Core.CoreExpr -> InferM m (Scheme TyCon)
infer u (Core.Var v) =
  case Core.isDataConId_maybe v of
    Just k
        -- Ignore typeclass evidence
      | Core.isClassTyCon $ Core.dataConTyCon k -> return $ Mono Ambiguous

        -- Infer constructor
      | otherwise -> do
        scheme <- fromCoreScheme u $ Core.varType v
        case decomp (body scheme) of
          -- Refinable datatype
          (fmap (unroll $ Core.dataConTyCon k) -> args, t@(Inj x d _)) -> do
            emit k x d
            mapM_ (\t -> emit t (inj x t)) args
            return scheme{ body = foldr (:=>) t args }

          -- Unrefinedable
          _ -> return scheme

    -- Infer variable
    Nothing -> emit v

-- Type literal
infer u l@(Core.Lit _) = fromCoreScheme u $ Core.exprType l

-- Type application
infer u (Core.App e1 (Core.Type e2)) = do
  t <- fromCore u e2
  scheme <- infer u e1
  when (isConstructor e1) $
    case decomp (body scheme) of
      (_, Inj x d _) -> emit t (inj x t)
      _              -> return ()

  return (applyScheme scheme t)

-- Term application
infer u (Core.App e1 e2) = infer u e1 >>= \case
  Forall as Ambiguous -> Forall as Ambiguous <$ infer u e2

  -- This should raise a warning for as /= []!
  Forall as (t3 :=> t4) -> do
    t2 <- mono <$> infer u' e2
    emit t2 t3
    return $ Forall as t4
    where
      u'
        | isConstructor e1
        , (_, Inj _ d _) <- decomp t4 = sum d : u
        | otherwise = u

  _ -> pprPanic "Term application to non-function!" $ ppr (Core.exprType e1, Core.exprType e2)

infer u (Core.Lam x e)
  | Core.isTyVar x = do
    -- Type abstraction
    a <- getExternalName x
    infer u e >>= \case
      Forall as t -> return $ Forall (a:as) t

  | otherwise = do
    -- Variable abstraction
    t1 <- fromCore u $ Core.varType x
    putVar (getName x) (Mono t1) (infer u e) >>= \case
      Forall as t2 -> return $ Forall as (t1 :=> t2)

-- Local prog
infer u (Core.Let b e) = do
  ts <- inferRec b
  putVars ts $ infer u e

infer u (Core.Case e bind_e core_ret alts) = do
  -- Fresh return type
  ret <- fromCore u core_ret

  -- Separate default case
  let altf = filter (\(_, _, rhs) -> not $ Core.exprIsBottom rhs) alts
  let (alts', def) = Core.findDefault altf

  -- Infer expression on which to pattern match
  t0 <- mono <$> infer u e

  -- Add the variable under scrutinee to scope
  putVar (getName bind_e) (Mono t0) $ case t0 of

    -- Infer a refinable case expression
    Inj rvar d _ -> do
      ks <- traverse (\(Core.DataAlt k, xs, rhs) -> do
          -- Add constructor arguments introduced by the pattern
          ts <- sequence $ M.fromList [ (n, Mono <$> fromCore (sum d:u) (Core.varType x))
                                      | x     <- xs,
                                        let n =  getName x ]

          branch e [k] rvar d $ do
            -- Constructor arguments are from the same refinement environment
            mapM_ (\(Mono kti) -> emit (inj rvar kti) kti) ts

            -- Ensure return type is valid
            ret_i <- mono <$> putVars ts (infer u rhs)
            emit ret_i ret

          -- Record constructors
          return k
        ) alts'

      case def of
        Nothing -> do
          -- Ensure destructor is total if not nested
          top <- topLevel e
          when top $ emit rvar d ks
        Just rhs ->
          -- Guard default case by constructors that have not occured
          branch e (tyConDataCons (sum d) L.\\ ks) rvar d $ do
            ret_i <- mono <$> infer u rhs
            emit ret_i ret

    -- Infer an unrefinable case expression
    Base d _ ->
      mapM_ (\(_, xs, rhs) -> do
        -- Add constructor arguments introduced by the pattern
        ts <- sequence $ M.fromList [ (n, Mono <$> fromCore (d:u) (Core.varType x))
                                    | x     <- xs,
                                      let n =  getName x ]

        -- Ensure return type is valid
        ret_i <- mono <$> putVars ts (infer u rhs)
        emit ret_i ret
      ) altf

  return $ Mono ret

-- Track source location
infer u (Core.Tick Core.SourceNote { Core.sourceSpan = s } e) = setLoc (RealSrcSpan s) $ infer u e

-- Ignore other ticks
infer u (Core.Tick _ e) = infer u e

-- Infer cast
infer u (Core.Cast e _) = do
  infer u e
  return (Mono Ambiguous)

-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ _ = error "Unimplemented"
