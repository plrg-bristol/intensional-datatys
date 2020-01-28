{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module InferCoreExpr (
  inferProg
) where

import Control.Monad

import qualified Data.List as L
import qualified Data.Map as M

import qualified GhcPlugins as Core

import Types
import Constraint
import InferM

-- Infer recursive bind
inferRec :: Monad m => Core.Bind Core.Var -> InferM m Context
inferRec bgs = do
  -- Add each binds within the group to context with a fresh type and no constraints
  binds <- foldM (\bs (Core.getName -> x, Core.exprType -> t) -> do
    Forall as t' <- fromCoreScheme t
    return $ M.insert x (RefinedScheme as [] empty t') bs
    ) M.empty $ Core.flattenBinds [bgs]

  -- Restrict type schemes
  restrict (head $ Core.rhssOfBind bgs) $
    -- Add recusrive binds and context build so far
    putVars binds $
      foldM (\bs (Core.getName -> x, rhs) -> do

        -- Infer each bind within the group, compiling constraints
        t@(Forall as ut) <- infer rhs

        -- Insure types are quantified by infered constraint
        let (RefinedScheme as' _ _ ut') = binds M.! x
        unless (as == as') $ Core.pprPanic "Type variables don't align!" (Core.ppr (as, as'))
        emitSubType ut  ut' rhs
        emitSubType ut' ut rhs

        return $ M.insert x t bs
        ) M.empty $ Core.flattenBinds [bgs]


-- Infer program
inferProg :: Monad m => Core.CoreProgram -> InferM m Context
inferProg = foldM (\ctx bgs -> putVars ctx (M.union ctx <$> inferRec bgs)) M.empty

-- Demand a monomorphic type
-- This is only applied to the lhs of (->) and case expressions
rank1 :: Monad m => m (Scheme T) -> m (Type T)
rank1 m = do
  Forall as t <- m
  case as of
    [] -> return t
    _  -> Core.pprPanic "Higher rank types are unimplemented." (Core.ppr (as, t))


infer :: Monad m => Core.Expr Core.Var -> InferM m (Scheme T)
infer e@(Core.Var x) =
  case Core.isDataConId_maybe x of
    Just k
      | Core.isClassTyCon $ Core.dataConTyCon k
            -> return $ Forall [] Ambiguous -- Ignore typeclass evidence

      | otherwise -> do -- Infer Constructor
        t@(Forall as t') <- fromCoreScheme $ Core.exprType e
        let (args, res)  =  result t'
        case res of
          Inj x d _ -> do
            l <- getTag
            emitSingle (con (Core.getName k) l) (Dom x (Core.getName d)) e
            mapM_ (\t -> emitSubType t (inj x t) e) args

          Base _ _ -> return () -- Unrefinable
        return t

    -- Infer variable
    Nothing -> getVar x e

infer l@(Core.Lit _) = fromCoreScheme $ Core.exprType l


-- Type application
infer (Core.App e1 (Core.Type e2)) = do
  t1 <- infer e1
  t2 <- fromCore e2
  return $ applyType t1 t2


-- Term application
infer e@(Core.App e1 e2) = do
  Forall as t1 <- infer e1
  case t1 of
    Ambiguous -> do
      t2 <- infer e2
      return $ Forall [] Ambiguous
    t3 :=> t4 -> do
      t2 <- rank1 $ infer e2
      emitSubType t2 t3 e
      return $ Forall as t4
    _ -> Core.pprPanic "Term application to non-function!" (Core.ppr (Core.exprType e1, Core.exprType e2))


infer e'@(Core.Lam x e)
  | Core.isTyVar x = do
    --Type abstraction
    Forall as t <- infer e
    return $ Forall (Core.getName x:as) t
  | otherwise = do
    -- Variable abstraction
    t1 <- fromCore $ Core.varType x
    Forall as t2 <- putVar (Core.getName x) (RefinedScheme [] [] empty t1) (infer e)
    return $ Forall as (t1 :=> t2)

-- Local prog
infer (Core.Let b e) = inferRec b >>= flip putVars (infer e)

infer e'@(Core.Case e b rt alts) = do
  -- The location of the case statement
  l <- getTag

  -- Fresh return type
  t <- fromCore rt

  -- Infer expression on which to pattern match
  t0 <- rank1 $ infer e

  -- Add the variable under scrutinee to scope
  putVar (Core.getName b) (RefinedScheme [] [] empty t0) $ case t0 of

    -- Infer a refinable case expression
    Inj x d _ -> do

      let (alts', def) = Core.findDefault alts
      ks <- foldM (\ks (Core.DataAlt (Core.getName -> k), bs, rhs) ->
        if Core.exprIsBottom rhs
          then return ks -- If rhs is bottom, it is not a valid case

          else do
            -- Add constructor arguments introduced by the pattern
            ts <- foldM (\m b -> do
              t <- fromCore $ Core.varType b
              return $ M.insert (Core.getName b) (RefinedScheme [] [] empty t) m
              ) M.empty bs

            branch e k x (Core.getName d) $ do
              -- Constructor arguments are from the same refinement environment
              mapM_ (\(RefinedScheme [] _ _ t) -> emitSubType (inj x t) t rhs) ts

              -- Ensure return type is valid
              ti' <- rank1 $ putVars ts (infer rhs)
              emitSubType ti' t rhs

              -- Track the occurance of a constructors
              return (k:ks)

        ) [] alts'

      tl <- topLevel e

      -- Ensure destructor is total if not nested
      case def of
        Nothing -> when tl $ emitSingle (Dom x (Core.getName d)) (set ks l) e'
        Just rhs
          | Core.exprIsBottom rhs -> when tl $ emitSingle (Dom x (Core.getName d)) (set ks l) e' -- If rhs is bottom, it is not a valid case
          | otherwise ->
            -- Default case
            -- Guard by constructors which have not occured
            branchAlts e [guardDom k x (Core.getName d) | k <- fmap Core.getName (Core.tyConDataCons d) L.\\ ks] $ do
              ti' <- rank1 $ infer rhs
              emitSubType ti' t rhs

    -- Infer an unrefinable case expression
    _ ->
      mapM_ (\(alt, bs, rhs) ->
        if Core.exprIsBottom rhs
          then return () -- If rhs is bottom, it is not a valid case
          else do
            -- Add constructor arguments introduced by the pattern
            ts <- foldM (\m b -> do
              t <- fromCore $ Core.varType b
              return $ M.insert (Core.getName b) (RefinedScheme [] [] empty t) m
              ) M.empty bs

            -- Ensure return type is valid
            ti' <- rank1 $ putVars ts (infer rhs)
            emitSubType ti' t rhs
        ) alts

  return $ Forall [] t

-- Track source location
infer (Core.Tick t e) = setLoc (Core.sourceSpan t) $ infer e

-- Infer cast
infer (Core.Cast e _) = do
  infer e
  return $ Forall [] Ambiguous

-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"
