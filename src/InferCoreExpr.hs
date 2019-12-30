{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module InferCoreExpr (
) where

import Control.Monad

import qualified Data.Map as M

import qualified GhcPlugins as Core

import Utils
import Types
import Constraint
import InferM
-- 
-- -- List all free variables in an expression
-- freeVars :: Core.Expr Core.Var -> [Core.Name]
-- freeVars (Core.Var i)         = [Core.getName i]
-- freeVars (Core.Lit _)         = []
-- freeVars (Core.App e1 e2)     = freeVars e1 ++ freeVars e2
-- freeVars (Core.Lam x e)       = freeVars e L.\\ [Core.getName x]
-- freeVars (Core.Let b e)       = (freeVars e ++ concatMap freeVars (Core.rhssOfBind b)) L.\\ (Core.getName <$> Core.bindersOf b)
-- freeVars (Core.Case e x _ as) = freeVars e ++ (concat [freeVars ae L.\\ (Core.getName <$> bs) | (_, bs, ae) <- as] L.\\ [Core.getName x])
-- freeVars (Core.Cast e _)      = freeVars e
-- freeVars (Core.Tick _ e)      = freeVars e
-- freeVars (Core.Type _)        = []
-- freeVars (Core.Coercion _)    = []
-- 
-- -- Used to compare groups of binds
-- instance Eq Core.CoreBind where
--   b == b' = Core.bindersOf b == Core.bindersOf b'
-- 
-- -- Sort a program in order of dependancies
-- dependancySort :: Core.CoreProgram -> Core.CoreProgram
-- dependancySort p = foldl go [] depGraph
--   where
--     -- Pair binder groups with their dependancies
--     depGraph = [(b, [group | rhs <- Core.rhssOfBind b, fv <- freeVars rhs, group <- findGroup p fv, group /= b]) | b <- p]
-- 
--     go p' (b, deps) = L.nub $
--       case L.elemIndex b p' of
--         Just i -> uncurry (++) $ first (++ deps) $ splitAt i p' -- Insert dependencies before binder
--         _      -> p' ++ deps ++ [b]                             -- Concatenate dependencies and binder to the end of the program
--     
--     -- Find the group in which the variable is contained
--     findGroup [] _ = []
--     findGroup (b:bs) x
--       | x `elem` (Core.getName <$> Core.bindersOf b) = [b]
--       | otherwise = findGroup bs x
-- 
-- -- Infer program
-- inferProg :: Core.CoreProgram -> InferM [(Core.Name, TypeScheme)]
-- inferProg p = do
-- 
--   -- Reorder program with dependancies
--   let p' = dependancySort p
-- 
--   -- Mut rec groups
--   z <- foldr (\b r -> do
-- 
--     -- Filter evidence binds
--     let xs   = Core.getName <$> filter (not . Core.isPredTy . Core.varType) (Core.bindersOf b)
--     let rhss = filter (not . Core.isPredTy . Core.exprType) $ Core.rhssOfBind b
-- 
--     -- Fresh typescheme for each binder in the group
--     ts <- mapM (freshScheme . Core.exprType) rhss
-- 
--     -- Infer constraints for the rhs of each bind
--     binds <- mapM (local (insertMany xs ts) . infer) rhss
--     let (ts', cgs) = unzip binds
-- 
--     -- !() <- Core.pprTraceM "Binds" (Core.ppr binds)
-- 
--     -- Combine constraint graphs
--     let bcg = foldr union empty cgs 
-- 
--     -- Insure fresh types are quantified by infered constraint (t' < t) for recursion
--     -- Type/refinement variables bound in match those bound in t'
--     let bcg' = foldr (\(rhs, t', Forall _ _ t) bcg' -> emit t' t (Just []) bcg' rhs) bcg (zip3 rhss ts' ts)
-- 
--     -- Restrict constraints to the interface
--     !ts'' <- quantifyWith bcg' ts
-- 
--     -- Add infered typescheme to the environment
--     r' <- local (insertMany xs ts'') r
-- 
--     return $ (xs, ts''):r'
--     ) (return []) p'
--   return $ concatMap (uncurry zip) z
-- 
--inferVar :: Core.Var -> [Core.Type] -> Core.Expr Core.Var -> InferM m (Type M T)
-- inferVar x ts e | Core.pprTrace "inferVar" (Core.ppr e) False = undefined 
-- inferVar x ts e =
--   case Core.isDataConId_maybe x of
--     Just k -> do 
--       (t, args) <- safeCon k ts
-- 
--       case t of
--         Inj x (Core.getName -> d) -> do
--           -- Infer refinable constructor
--           forM_ args (\a -> emitT a (inj x a) e)
--           emitS (Con (Core.getName k)) (Dom x d) 
--       
--       return (foldr (:=>) t args)
-- 
--     Nothing -> do  
--       -- Infer polymorphic variable at type(s)
--       t <- safeVar x ts 
--       v <- fromCore $ Core.exprType e
--       emitT t v e 
--       return (v, t)

infer :: Monad m => Core.Expr Core.Var -> InferM m (Scheme T)
infer (Core.Var x) =
  case Core.isDataConId_maybe x of
    -- Infer constructor
    Just k  -> fromCore $ Core.dataConUserType k

    -- Infer variable
    Nothing -> safeVar x 

infer l@(Core.Lit _) = fromCore $ Core.exprType l

infer e@(Core.App e1 e2) =
  case e2 of
    Core.Type t -> do
      -- Type appliciation
      t1 <- infer e1
      applyTyVars t1 t

    _ -> do
      -- Term appliciation
      t1 <- infer e1
      if Core.isPredTy (Core.exprType e2) 
        then return t1
        else case mono t1 of
          t3 :=> t4 -> do
            t2 <- infer e2
            emitT (mono t2) t3 e
            return (Forall [] t4) 

          _ -> Core.pprPanic "Application must be to an arrow type!" (Core.ppr e)

infer (Core.Lam x e) = do
  let t = Core.varType x
  if False -- type or term 
    then do
      -- Type abstraction
      t' <- infer e
      case t' of
        Forall as u -> return $ Forall (Core.getName x:as) u
    else do
      -- Variable abstraction
      t1 <- fromCore t
      t2 <- withVars [(Core.getName x, ([], M.empty, t1))] (infer e)
      return $ Forall [] (mono t1 :=> mono t2)
 
infer e'@(Core.Let b e) = do
  -- Infer local module (i.e. let expression)
  let xs   = Core.getName <$> Core.bindersOf b
  let rhss = Core.rhssOfBind b
 
  -- Add each binds within the group to context with a fresh type (t) and no constraints
  ts <- mapM (fromCore . Core.exprType) rhss
 
  ts' <- foldM (\ts rhs -> do
    -- Infer each bind within the group, compiling constraints
    t <- withVars (zip xs (fmap (\t -> ([], M.empty, t)) ts)) (infer rhs)
    return (ts ++ [t])
    ) [] rhss
 
  --  Insure fresh types are quantified by infered constraint (t' < t)
  mapM_ (\(r, Forall _ t', Forall _ t) -> emitT t' t r) (zip3 rhss ts' ts)
 
  -- Restrict constraints to the interface
  ts'' <- restrict ts
 
  -- Infer in body with infered typescheme to the environment
  withVars (zip xs ts'') (infer e)
-- 
--   -- Infer top-level case expession
-- infer e'@(Core.Case e b rt as) = do
--   -- Fresh return type
--   t  <- fresh rt
-- 
--   -- Infer expression on which to pattern match
--   (t0, c0) <- infer e
--   let d = case sort t0 of { SBase d -> d; SData d -> d }
-- 
--   -- b @ e
--   et <- fresh $ Core.exprType e
--   let c0' = emit et t0 (Just []) c0 e
-- 
--   (caseType, cg) <- local (insertVar (Core.getName b) $ Forall [] empty et) (pushCase e >> -- Add expression to the context, and record the case
--     foldM (\(caseType, cg) (a, bs, rhs) ->
--       if Core.exprIsBottom rhs
--         then return (caseType, cg) -- If rhs is bottom, it is not a valid case
--         else do
--           -- Add variables introduced by the pattern
--           ts <- mapM (fresh . Core.varType) bs
-- 
--           -- Ensure return type is valid
--           (ti', cgi) <- local (insertMany (Core.getName <$> bs) (Forall [] empty <$> ts)) (infer rhs)
--           let cgi' = emit ti' t (Just []) cgi e'
-- 
--           -- Track the occurance of a constructors/default case
--           case a of 
--             Core.DataAlt (Core.getName -> k) -> return (fmap (k:) caseType, cg `union` guardWith k t0 cgi')
--             _                                -> return (Nothing, cg `union` cgi') -- Default/literal cases
--     ) (Just [], c0') as)
-- 
--   popCase
-- 
--   tl <- topLevel e
-- 
--   -- Ensure destructor is total, GHC will conservatively insert defaults
--   case caseType of
--     Nothing  -> return (t, cg) -- Literal cases must have a default
--     Just ks -> 
--       if tl 
--         then return (t, emit t0 (Sum d ks) (Just []) cg e')
--         else return (t, cg)
--     _ -> Core.pprPanic "Inconsistent data constructors arguments!" (Core.ppr ())
-- 
-- -- Remove core ticks
-- infer (Core.Tick _ e) = infer e
-- 
-- -- Maintain constraints but give trivial type (Dot - a sub/super-type of everything) to expression - effectively ignore casts
-- -- GHC already requires the prog to well typed
-- infer (Core.Cast e _) = do
--   (_, cg) <- infer e
--   return (Dot, cg)
-- 
-- -- Cannot infer a coercion expression.
-- -- For most programs these will never occur outside casts.
-- infer _ = error "Unimplemented"
