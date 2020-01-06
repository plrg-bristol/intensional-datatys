{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

module InferCoreExpr (
  inferProg
) where

import Control.Monad
import Control.Arrow

import qualified Data.List as L
import qualified Data.Map as M

import qualified GhcPlugins as Core

import Utils
import Types
import Constraint
import InferM
 
-- List all free variables in an expression
freeVars :: Core.Expr Core.Var -> [Core.Name]
freeVars (Core.Var i)         = [Core.getName i]
freeVars (Core.Lit _)         = []
freeVars (Core.App e1 e2)     = freeVars e1 ++ freeVars e2
freeVars (Core.Lam x e)       = freeVars e L.\\ [Core.getName x]
freeVars (Core.Let b e)       = (freeVars e ++ concatMap freeVars (Core.rhssOfBind b)) L.\\ (Core.getName <$> Core.bindersOf b)
freeVars (Core.Case e x _ as) = freeVars e ++ (concat [freeVars ae L.\\ (Core.getName <$> bs) | (_, bs, ae) <- as] L.\\ [Core.getName x])
freeVars (Core.Cast e _)      = freeVars e
freeVars (Core.Tick _ e)      = freeVars e
freeVars (Core.Type _)        = []
freeVars (Core.Coercion _)    = []

-- Used to compare groups of binds
instance Eq Core.CoreBind where
  b == b' = Core.bindersOf b == Core.bindersOf b'

-- Sort a program in order of dependancies
dependancySort :: Core.CoreProgram -> Core.CoreProgram
dependancySort p = foldl go [] depGraph
   where
   -- Pair binder groups with their dependancies
    depGraph = [(b, [group | rhs <- Core.rhssOfBind b, fv <- freeVars rhs, group <- findGroup p fv, group /= b]) | b <- p]

    go p' (b, deps) = L.nub $
      case L.elemIndex b p' of
        Just i -> uncurry (++) $ first (++ deps) $ splitAt i p' -- Insert dependencies before binder
        _      -> p' ++ deps ++ [b]                             -- Concatenate dependencies and binder to the end of the program
    
    -- Find the group in which the variable is contained
    findGroup [] _ = []
    findGroup (b:bs) x
      | x `elem` (Core.getName <$> Core.bindersOf b) = [b]
      | otherwise = findGroup bs x

-- Infer program
inferProg :: Monad m => Core.CoreProgram -> InferM m [(Core.Name, ([Int], ConSet, Type T))]
inferProg p = do
 
  -- Reorder program with dependancies
  let p' = dependancySort p

  foldM (\l bg -> do
    -- Add each binds within the group to context with a fresh type (t) and no constraints
    binds <- mapM (\(Core.getName -> x, Core.exprType -> t) -> do 
      t' <- fromCore t
      return (x, t')
      ) $ Core.flattenBinds [bg]

    restrict [] -- Clear any refinement variables

    ts <- withVars l $ withVars' binds $ mapM (\(x, rhs) -> do

      -- Infer each bind within the group, compiling constraints
      t <- infer rhs

      -- Insure fresh types are quantified by infered constraint (t < t')
      t' <- safeVar x
      emitT t t' rhs

      return t
      ) $ Core.flattenBinds [bg]

    -- Restrict constraints to the interface
    ts' <- restrict ts
  
    return $ zip (Core.getName <$> Core.bindersOf bg) ts' ++ l
    ) [] p'

infer :: Monad m => Core.Expr Core.Var -> InferM m (Type T)
infer (Core.Var x) =
  case Core.isDataConId_maybe x of
    -- Infer constructor
    Just k  -> fromCore $ Core.dataConUserType k

    -- Infer variable
    Nothing -> safeVar x 

infer l@(Core.Lit _) = fromCore $ Core.exprType l

infer (Core.App e1 (Core.Type e2)) = do
  t1 <- infer e1
  applyTyVars t1 e2

infer e@(Core.App e1 e2) = do
  t1 <- infer e1
  case t1 of
    t3 :=> t4 -> do
      t2 <- infer e2
      emitT t2 t3 e
      return t4

infer (Core.Lam x e) =
  if not $ Core.isTyVar x
    then do
      -- Variable abstraction
      t1 <- fromCore $ Core.varType x
      t2 <- withVar' (Core.getName x) t1 (infer e)
      return (t1 :=> t2)
    else
      -- Type abstraction
      Forall (Core.getName x) <$> infer e
 
infer e'@(Core.Let b e) = do
  -- Add each binds within the group to context with a fresh type (t) and no constraints
  binds <- mapM (\(Core.getName -> x, Core.exprType -> t) -> do 
    t' <- fromCore t
    return (x, t')
    ) $ Core.flattenBinds [b]
 
  ts <- withVars' binds $ mapM (\(x, rhs) -> do
    -- Infer each bind within the group, compiling constraints
    t <- infer rhs

    -- Insure fresh types are quantified by infered constraint (t < t')
    t' <- safeVar x
    emitT t t' rhs    

    return t
    ) $ Core.flattenBinds [b] 
 
  -- Restrict constraints to the interface
  ts' <- restrict ts
  
  -- Infer in body with infered typescheme to the environment
  withVars (zip (Core.getName <$> Core.bindersOf b) ts') (infer e)
 
infer e'@(Core.Case e b rt as) = do
  -- Fresh return type
  t <- fromCore rt

  -- Infer expression on which to pattern match
  et <- fromCore $ Core.exprType e
  t0 <- infer e
    
  let (x, d) = case t0 of { Inj x d -> (Just x, Core.getName d); Base d -> (Nothing, Core.getName d); _ -> Core.pprPanic "Datatype isn't pattern matchtable" (Core.ppr t0)}

  emitT et t0 e

  pushCase e

  caseType <- withVar' (Core.getName b) et $ foldM (\caseType (a, bs, rhs) ->
    if Core.exprIsBottom rhs
      then return caseType -- If rhs is bottom, it is not a valid case
      else do
        -- Guard case
        let branch = case a of {Core.DataAlt (Core.getName -> k) -> case x of {Just x' -> guardWith x' k d; Nothing -> id} ; _ -> id }

        -- Add variables introduced by the pattern
        ts <- mapM (fromCore . Core.varType) bs
        
        -- Ensure return type is valid
        ti' <- withBranch branch $ withVars (zip (Core.getName <$> bs) (([], M.empty,) <$> ts)) (infer rhs)
        withBranch branch $ emitT ti' t e'

        -- Track the occurance of a constructors/default case
        case a of 
          Core.DataAlt (Core.getName -> k) -> return (fmap (k:) caseType)
          _                                -> return Nothing -- Default/literal cases
    ) (Just []) as
 
  popCase
 
  tl <- topLevel e 
  
  -- Ensure destructor is total, GHC will conservatively insert defaults
  case caseType of
    Nothing  -> return t -- Literal cases must have a default
    Just ks -> do
      case x of
        Just x' -> when tl (emitS (Dom x' d) (Set ks))
        Nothing -> return () 
      return t
 
-- Remove core ticks
infer (Core.Tick _ e) = infer e
 
infer e'@(Core.Cast e _) = do
  infer e
  fromCore $ Core.exprType e'
 
-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"
