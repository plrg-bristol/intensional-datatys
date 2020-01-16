{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module InferCoreExpr (
  inferProg
) where

import Control.Monad

import qualified Data.Map as M

import qualified GhcPlugins as Core

import Types
import Constraint
import InferM


-- Infer program
inferProg :: Core.MonadUnique m => Core.CoreProgram -> InferM m Context
inferProg = foldM (\ctx bgs -> do

  -- Add each binds within the group to context with a fresh type and no constraints
  binds <- foldM (\bs (Core.getName -> x, Core.exprType -> t) -> do
    Forall as t' <- fromCoreScheme t
    return $ M.insert x (RefinedScheme as [] empty t') bs
    ) M.empty $ Core.flattenBinds [bgs]

  -- Restrict type schemes
  ts <- restrict $
    -- Add recusrive binds and context build so far
    putVars binds $ putVars ctx $
      foldM (\bs (Core.getName -> x, rhs) -> do

        -- Infer each bind within the group, compiling constraints
        t@(Forall as ut) <- infer rhs

        -- Insure types are quantified by infered constraint
        let (RefinedScheme as' _ _ ut') = binds M.! x
        when (as /= as') $ Core.pprPanic "Type variables don't align!" (Core.ppr (as, as'))
        emitSubType ut  ut' rhs
        emitSubType ut' ut rhs

        return $ M.insert x t bs
        ) M.empty $ Core.flattenBinds [bgs]

  return (M.union ctx ts)
  ) M.empty


-- Demand a monomorphic type
rank1 :: Monad m => Core.Expr Core.Var -> m (Scheme T) -> m (Type T)
rank1 e m = do
  Forall as t <- m
  case as of
    [] -> return t
    _  -> Core.pprPanic "RankN types are unimplemented." (Core.ppr (as, t, e))


infer :: Core.MonadUnique m => Core.Expr Core.Var -> InferM m (Scheme T)
infer e@(Core.Var x) =
  case Core.isDataConId_maybe x of
    -- Infer constructor
    Just k -> do
      t@(Forall as t')  <- fromCoreScheme $ Core.exprType e
      let (args, res) = dataCon t'
      case res of
        Inj x d _ -> do
          emitSingle (con (Core.getName k)) (Dom x (Core.getName d)) top
          mapM_ (\t -> emitSubType t (inj x t) e) args

        Base _ _ -> return () -- Unrefinable
      return t

    -- Infer variable
    Nothing -> getVar x e
  where
    -- Extract the result type from a constructor
    dataCon :: Type T -> ([Type T], Type T)
    dataCon (a :=> b) = (a:args, res)
      where
        (args, res) = dataCon b
    dataCon t = ([], t)


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
    t3 :=> t4 -> do
      t2 <- rank1 e $ infer e2
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
    t2 <- rank1 e' $ putVar (Core.getName x) (RefinedScheme [] [] empty t1) (infer e)
    return $ Forall [] (t1 :=> t2)


infer e'@(Core.Let b e) = do
  -- Add each binds within the group to context with a fresh type and no constraints
  binds <- foldM (\bs (Core.getName -> x, Core.exprType -> t) -> do
    Forall as t' <- fromCoreScheme t
    return $ M.insert x (RefinedScheme as [] empty t') bs
    ) M.empty $ Core.flattenBinds [b]

  -- Restrict type schemes
  ts <- restrict $
    -- Add recusrive binds
    putVars binds $
      foldM (\bs (Core.getName -> x, rhs) -> do

        -- Infer each bind within the group, compiling constraints
        t@(Forall as ut) <- infer rhs

        -- Insure types are quantified by infered constraint
        let (RefinedScheme as' _ _ ut') = binds M.! x
        when (as /= as') $ Core.pprPanic "Type variables don't align!" (Core.ppr (as, as'))
        emitSubType ut  ut' rhs
        emitSubType ut' ut rhs

        return $ M.insert x t bs
        ) M.empty $ Core.flattenBinds [b]

  -- Infer in body with infered typescheme to the environment
  putVars ts (infer e)

infer e'@(Core.Case e b rt alts) = do
  pushCase e

  -- Fresh return type
  t <- fromCore rt

  -- Infer expression on which to pattern match
  t0 <- rank1 e' $ infer e

  -- Add the variable under scrutinee to scope
  putVar (Core.getName b) (RefinedScheme [] [] empty t0) $ case unInj t0 of

    -- Infer a refinable case expression
    Just (x, d) -> do
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


            branch k x (Core.getName d) $ do
              -- Constructor arguments are from the same refinement environment
              mapM_ (\(RefinedScheme [] _ _ t) -> emitSubType (inj x t) t rhs) ts

              -- Ensure return type is valid
              ti' <- rank1 e' $ putVars ts (infer rhs)
              emitSubType ti' t rhs

              -- Track the occurance of a constructors
              return (k:ks)
        ) [] alts'

      -- Ensure destructor is total if not nested
      popCase
      tl <- topLevel e

      -- branchAlts [guardDom k x (Core.getName d) | k <- (fmap Core.getName $ Core.tyConDataCons d) L.\\ ks] $
      case def of
        Nothing -> when tl $ emit (insert (Dom x (Core.getName d)) (set ks) top empty)
        Just rhs
          | Core.exprIsBottom rhs -> when tl $ emit (insert (Dom x (Core.getName d)) (set ks) top empty) -- If rhs is bottom, it is not a valid case
          | otherwise -> do
            -- Default case
            ti' <- rank1 e' $ infer rhs
            emitSubType ti' t rhs

    -- Infer an unrefinable case expression
    Nothing -> do
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
            ti' <- rank1 e' $ putVars ts (infer rhs)
            emitSubType ti' t rhs
        ) alts
      popCase

  return $ Forall [] t
    where
      unInj :: Type T -> Maybe (Int, Core.TyCon)
      unInj (Inj x d as) = Just (x, d)
      unInj _            = Nothing

-- Remove core ticks
infer (Core.Tick _ e) = infer e

infer e'@(Core.Cast e _) = do
  infer e
  fromCoreScheme $ Core.exprType e'

-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"
