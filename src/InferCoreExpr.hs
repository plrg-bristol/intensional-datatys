{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module InferCoreExpr (
  inferProg
) where

import Control.Monad

import qualified GhcPlugins as Core

import Types
import Constraint
import InferM

data CaseType = RefinedDataAlt Int Core.Name | BaseAlt

-- Infer program
inferProg :: Monad m => Core.CoreProgram -> InferM m [(Core.Name, TypeScheme)]
inferProg = foldM (\l bg -> do
  restrict []

  -- Add each binds within the group to context with a fresh type (t) and no constraints
  binds <- mapM (\(Core.getName -> x, Core.exprType -> t) -> do 
    t' <- fromCore t
    return (x, TypeScheme ([], empty, t'))
    ) $ Core.flattenBinds [bg]

  ts <- putVars binds $ putVars l $ mapM (\(x, rhs) -> do
    -- Infer each bind within the group, compiling constraints
    t <- infer rhs

    -- Insure fresh types are quantified by infered constraint (t < t')
    t' <- getVar x rhs
    emitSubType t t' rhs

    return (Core.getName x, t)
    ) $ Core.flattenBinds [bg]

  -- Restrict type schemes
  ts' <- restrict ts

  return (l ++ ts')
  ) []

infer :: Monad m => Core.Expr Core.Var -> InferM m (Type T)
infer e@(Core.Var x) =
  case Core.isDataConId_maybe x of
    -- Infer constructor
    Just k -> do
      t  <- fromCore $ Core.exprType e
      let (args, res) = dataCon t
      case res of
        Inj x d -> do
          emit (insert (Con (Core.getName k)) (Dom x (Core.getName d)) top empty)
          mapM_ (\t -> emitSubType t (inj x t) e) args
        Base _ -> return () -- Unrefinable
      return t

    -- Infer variable
    Nothing -> getVar x e

infer l@(Core.Lit _) = fromCore $ Core.exprType l

infer (Core.App e1 (Core.Type e2)) = do
  t1 <- infer e1
  case t1 of
    Forall a u -> subTyVarM a e2 u
    _ -> Core.pprPanic "Type application to monotype!" (Core.ppr (Core.exprType e1,  e2))

infer e@(Core.App e1 e2) = do
  t1 <- infer e1
  case t1 of
    t3 :=> t4 -> do
      t2 <- infer e2
      emitSubType t2 t3 e
      return t4
    _ -> Core.pprPanic "Term application to non-function!" (Core.ppr (Core.exprType e1, Core.exprType e2))

infer (Core.Lam x e) =
  if Core.isTyVar x
    then 
      -- Type abstraction
      Forall (Core.getName x) <$> infer e
    else do
      -- Variable abstraction
      t1 <- fromCore $ Core.varType x
      t2 <- putVar (Core.getName x) (TypeScheme ([], empty, t1)) (infer e)
      return (t1 :=> t2)
 
infer e'@(Core.Let b e) = do
  -- Add each binds within the group to context with a fresh type (t) and no constraints
  binds <- mapM (\(Core.getName -> x, Core.exprType -> t) -> do 
    t' <- fromCore t
    return (x, TypeScheme ([], empty, t'))
    ) $ Core.flattenBinds [b]
 
  ts <- putVars binds $ mapM (\(x, rhs) -> do
    -- Infer each bind within the group, compiling constraints
    t <- infer rhs

    -- Insure fresh types are quantified by infered constraint (t < t')
    t' <- getVar x e'
    emitSubType t t' rhs

    return (Core.getName x, t)
    ) $ Core.flattenBinds [b] 
 
  -- Restrict constraints to the interface
  ts' <- restrict ts
  
  -- Infer in body with infered typescheme to the environment
  putVars ts' (infer e)
 
infer e'@(Core.Case e b rt alts) = do
  pushCase e

  -- Fresh return type
  t <- fromCore rt

  -- Infer expression on which to pattern match
  t0 <- infer e

  -- Add the variable under scrutinee to scope
  putVar (Core.getName b) (TypeScheme ([], empty, t0)) $  case unInj t0 of

      -- Infer a refinable case expression
      Just (x, d) -> do
        let (alts', def) = Core.findDefault alts
        ks <- foldM (\ks (Core.DataAlt (Core.getName -> k), bs, rhs) ->
          if Core.exprIsBottom rhs
            then return ks -- If rhs is bottom, it is not a valid case
            else do
              -- Add constructor arguments introduced by the pattern
              ts <- mapM (\b -> (Core.getName b,) . (\t -> TypeScheme ([], empty, t)) <$> (fromCore $ Core.varType b)) bs

              branch k x d $ do
                -- Constructor arguments are from the same refinement environment
                mapM_ (\t -> emitSubType (inj x t) t rhs) $ fmap (\(_, TypeScheme (_, _, t)) -> t) ts
                
                -- Ensure return type is valid
                ti' <- putVars ts (infer rhs)
                emitSubType ti' t rhs

                -- Track the occurance of a constructors
                return (k:ks)
            ) [] alts'

        -- Ensure destructor is total if not nested  
        popCase
        tl <- topLevel e

        branchAlts [dom k x d | k <- ks] $ case def of
          Nothing -> when tl $ emit (insert (Dom x (Core.getName d)) (Set ks) top empty)
          Just rhs
            | Core.exprIsBottom rhs -> do -- If rhs is bottom, it is not a valid case
                when tl $ emit (insert (Dom x (Core.getName d)) (Set ks) top empty)
            | otherwise -> do
                -- Default case
                ti' <- infer rhs
                emitSubType ti' t rhs

      -- Infer an unrefinable case expression
      Nothing -> do
        mapM_ (\(alt, bs, rhs) ->
          if Core.exprIsBottom rhs
            then return () -- If rhs is bottom, it is not a valid case
            else do
              -- Add constructor arguments introduced by the pattern
              ts <- mapM (\b -> (Core.getName b,) . (\t -> TypeScheme ([], empty, t)) <$> (fromCore $ Core.varType b)) bs
              
              -- Ensure return type is valid
              ti' <- putVars ts (infer rhs)
              emitSubType ti' t rhs
            ) alts
        popCase

  return t
  where
    unInj :: Type T -> Maybe (Int, Core.Name)
    unInj (Inj x d) = Just (x, Core.getName d)
    unInj (App a b) = unInj a
    unInj _         = Nothing
 
-- Remove core ticks
infer (Core.Tick _ e) = infer e
 
infer e'@(Core.Cast e _) = do
  infer e
  fromCore $ Core.exprType e'
 
-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"
