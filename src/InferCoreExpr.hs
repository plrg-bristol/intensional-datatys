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
    return (x, TypeScheme ([], empty, t'))
    ) $ Core.flattenBinds [bg]

  ts <- putVars binds $ putVars l $ mapM (\(x, rhs) -> do
    -- Infer each bind within the group, compiling constraints
    t <- infer rhs

    -- Insure fresh types are quantified by infered constraint (t < t')
    t' <- getVar x rhs
    emitSubType t t' rhs
    emitSubType t' t rhs

    return (Core.getName x, t)
    ) $ Core.flattenBinds [bg]

  -- Restrict type schemes
  ts' <- restrict ts

  return (ts' ++ l)
  ) []

infer :: Monad m => Core.Expr Core.Var -> InferM m (Type T)
infer e@(Core.Var x) =
  case Core.isDataConId_maybe x of
    -- Infer constructor
    Just k -> do
      t  <- fromCore $ Core.dataConRepType k
      let (args, res) = dataCon t
      case res of
        Inj x d -> do
          emit (insert (Con (Core.getName k)) (Dom x (Core.getName d)) top empty)
          mapM_ (\t -> emitSubType t (inj x t) e) args 
        _ -> return () -- Unrefinable    
      return t

    -- Infer variable
    Nothing -> getVar x e

infer l@(Core.Lit _) = fromCore $ Core.exprType l

infer (Core.App e1 (Core.Type e2)) = do
  t1 <- infer e1
  case t1 of 
    Forall a u -> do
      t2 <- fromCore e2
      return $ subTyVar a t2 u
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
    emitSubType t' t rhs 

    return (Core.getName x, t)
    ) $ Core.flattenBinds [b] 
 
  -- Restrict constraints to the interface
  ts' <- restrict ts
  
  -- Infer in body with infered typescheme to the environment
  putVars ts' (infer e)
 
infer e'@(Core.Case e b rt as) = do
  -- Fresh return type
  t <- fromCore rt

  -- Infer expression on which to pattern match
  t0 <- infer e

  pushCase e

  caseType <- putVar (Core.getName b) (TypeScheme ([], empty, t0)) $ foldM (\caseType (a, bs, rhs) ->
    if Core.exprIsBottom rhs
      then return caseType -- If rhs is bottom, it is not a valid case
      else do
        -- Add variables introduced by the pattern
        ts <- mapM (\b -> (Core.getName b,) . (\t -> TypeScheme ([], empty, t)) <$> (fromCore $ Core.varType b)) bs

        case a of
          Core.DataAlt k
            | Inj x (Core.getName -> d) <- t0 ->
              branch (Core.getName k) x d $ do
                 -- Ensure return type is valid
                ti' <- putVars ts (infer rhs)

                mapM_ (\t -> emitSubType (inj x t) t rhs) $ fmap (\(_, TypeScheme (_, _, t)) -> t) ts
                emitSubType ti' t rhs  

          _ -> do
            ti' <- putVars ts (infer rhs)
            emitSubType ti' t rhs

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
      | Inj x (Core.getName -> d) <- t0
      , tl -> emit (insert (Dom x d) (Set ks) top empty)
    _      -> return () -- Literal cases must have a default
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
