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

-- Infer program
inferProg :: Monad m => Core.CoreProgram -> InferM m [(Core.Name, TypeScheme)]
inferProg = foldM (\l bg -> do
  -- Add each binds within the group to context with a fresh type (t) and no constraints
  binds <- mapM (\(Core.getName -> x, Core.exprType -> t) -> do 
    t' <- fromCore t
    return (x, simple t')
    ) $ Core.flattenBinds [bg]

  ts <- putVar binds $ putVar l $ mapM (\(x, rhs) -> do
    -- Infer each bind within the group, compiling constraints
    t <- infer rhs

    -- Insure fresh types are quantified by infered constraint (t < t')
    t' <- getVar x
    emitSubType t t' rhs

    return (Core.getName x, t)
    ) $ Core.flattenBinds [bg]

  -- Restrict type schemes
  ts' <- restrict ts

  return (ts' ++ l)
  ) []

infer :: Monad m => Core.Expr Core.Var -> InferM m (Type T)
infer (Core.Var x) =
  case Core.isDataConId_maybe x of
    -- Infer constructor
    Just k -> do
      t <- fromCore $ Core.dataConUserType k
      case t of
        Inj x (Core.getName -> d) -> emit (singleton (Con $ Core.getName k) (Dom x d) mempty)
        _ -> return ()
      return t

    -- Infer variable
    Nothing -> getVar x 

infer l@(Core.Lit _) = fromCore $ Core.exprType l

infer (Core.App e1 (Core.Type e2)) = do
  t1 <- infer e1
  case t1 of 
    Forall a t2 -> subTyVar a t2 e2

infer e@(Core.App e1 e2) = do
  t1 <- infer e1
  case t1 of
    t3 :=> t4 -> do
      t2 <- infer e2
      emitSubType t2 t3 e
      return t4

infer (Core.Lam x e) =
  if not $ Core.isTyVar x
    then do
      -- Variable abstraction
      t1 <- fromCore $ Core.varType x
      t2 <- putVar [(Core.getName x, simple t1)] (infer e)
      return (t1 :=> t2)
    else
      -- Type abstraction
      Forall (Core.getName x) <$> infer e
 
infer e'@(Core.Let b e) = do
  -- Add each binds within the group to context with a fresh type (t) and no constraints
  binds <- mapM (\(Core.getName -> x, Core.exprType -> t) -> do 
    t' <- fromCore t
    return (x, simple t')
    ) $ Core.flattenBinds [b]
 
  ts <- putVar binds $ mapM (\(x, rhs) -> do
    -- Infer each bind within the group, compiling constraints
    t <- infer rhs

    -- Insure fresh types are quantified by infered constraint (t < t')
    t' <- getVar x
    emitSubType t t' rhs    

    return (Core.getName x, t)
    ) $ Core.flattenBinds [b] 
 
  -- Restrict constraints to the interface
  ts' <- restrict ts
  
  -- Infer in body with infered typescheme to the environment
  putVar ts' (infer e)
 
infer e'@(Core.Case e b rt as) = do
  -- Fresh return type
  t <- fromCore rt

  -- Infer expression on which to pattern match
  t0 <- infer e
  let (x, d) = unInj t0

  pushCase e

  caseType <- putVar [(Core.getName b, simple t0)] $ foldM (\caseType (a, bs, rhs) ->
    if Core.exprIsBottom rhs
      then return caseType -- If rhs is bottom, it is not a valid case
      else do
        -- Add variables introduced by the pattern
        ts <- mapM (\b -> (Core.getName b,) . simple <$> (fromCore $ Core.varType b)) bs

        -- Guard case (if t0 is refinable)
        let (Core.DataAlt (Core.getName -> k)) = a
        let guard = maybe id (\x -> branch k x d) x
        
        guard $ do
          -- Ensure return type is valid
          ti' <- putVar ts (infer rhs)
          emitSubType ti' t e'

        -- Track the occurance of a constructors/default case
        case a of 
          Core.DataAlt (Core.getName -> k) -> return (fmap (k:) caseType)
          _                                -> return Nothing -- Default/literal cases
    ) (Just []) as
 
  popCase
 
  tl <- topLevel e 
  
  -- Ensure destructor is total, GHC will conservatively insert defaults    
  case caseType of
    Just ks
      | Just x' <- x, tl -> emit (singleton (Dom x' d) (Set ks) mempty)
    _                    -> return () -- Literal cases must have a default
  return t

  where
    unInj :: Type T -> (Maybe Int, Core.Name) 
    unInj (Inj x (Core.getName -> n)) = (Just x, n)
    unInj (Base  (Core.getName -> n)) = (Nothing, n)
    unInj t0                          = Core.pprPanic "Datatype isn't pattern matchtable" (Core.ppr t0)
 
-- Remove core ticks
infer (Core.Tick _ e) = infer e
 
infer e'@(Core.Cast e _) = do
  infer e
  fromCore $ Core.exprType e'
 
-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"
