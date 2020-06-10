{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}

module InferCoreExpr
  ( inferProg,
  )
where

import Constructors
import Control.Monad.RWS.Strict
import CoreUtils
import qualified Data.List as L
import qualified Data.Map as M
import DataTypes
import FromCore
import qualified GhcPlugins as Core
import InferM
import Name
import Outputable hiding (empty)
import Scheme
import TyCon
import Types
import Prelude hiding (sum)

-- defaultLevel :: d -> InferM s (DataType d)
-- defaultLevel k = do
--   u <- asks unrollDataTypes
--   if u then return (DataType Initial k) else return (DataType Neutral k)

-- Infer constraints for a (mutually-)recursive bind
inferRec :: Bool -> Core.CoreBind -> InferM Context
inferRec top bgs = do
  binds <-
    sequence $
      M.fromList
        [ (n, fromCoreScheme (exprType rhs))
          | (x, rhs) <- Core.flattenBinds [bgs],
            let n = getName x
        ]
  ctx <-
    putVars binds -- Add binds for recursive calls
      $
      -- Infer rhs; subtype of recursive usage
      sequence
      $ M.fromList
        [ ( n,
            do
              scheme <- infer rhs
              inferSubType (body scheme) (body sr)
              inferSubType (body sr) (body scheme)
              return scheme
          )
          | (x, rhs) <- Core.flattenBinds [bgs],
            let n = getName x,
            let sr = binds M.! n
        ]
  if top
    then InferM.saturate ctx -- If generalising let or a top-level definition
    else return ctx

-- Infer constraints for a module
inferProg :: Core.CoreProgram -> InferM Context
inferProg = foldM (\ctx -> fmap (M.union ctx) . putVars ctx . inferRec True) M.empty

inferSubType :: Type 'T -> Type 'T -> InferM ()
inferSubType (Var _) (Var _) = return ()
inferSubType Ambiguous _ = return ()
inferSubType _ Ambiguous = return ()
inferSubType t1 t2
  | shape t1 /= shape t2 = do
    l <- asks inferLoc
    pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
inferSubType (t11 :=> t12) (t21 :=> t22) =
  inferSubType t21 t11 >> inferSubType t12 t22
inferSubType (Inj x d as) (Inj y d' _)
  | x /= y && d /= d' = do
    -- Combine Initial and Full datatype constraints
    cg <- gets InferM.constraints
    -- cg' <- mergeLevel x y (fmap getName d) (fmap getName d') cg
    -- modify (\s -> s {Scheme.constraints = cg'})
    emit (Dom x (getName <$> d)) (Dom y (getName <$> d'))
    slice x y (d, as)
inferSubType _ _ = return ()

-- Take the slice of a datatype including parity
slice :: Int -> Int -> (DataType TyCon, [Type 'S]) -> InferM ()
slice x y = void. loop [] True
  where
    loop :: [TyCon] -> Bool -> (DataType TyCon, [Type 'S]) -> InferM [TyCon]
    loop ds p (d, as)
      | trivial (orig d) || orig d `elem` ds = return ds
      | otherwise = do
        -- c <- asks allowContra
        foldM
          ( \ds' k ->
              ( branchWithoutExpr k x (level d)
                -- if c
                --   then branch' [k] x d -- If contraviarnt consturctors are permitted slices need to be guarded
                --   else id
              )
                $ do
                  k_ty <- fromCoreConsInst (k <$ d) as
                  foldM (`step` p) ds' (fst $ decompTy k_ty)
          )
          ds
          (tyConDataCons $ orig d)
    step :: [TyCon] -> Bool -> Type 'T -> InferM [TyCon]
    step ds p (Inj _ d' as') = do
      if p
        then emit (Dom x (getName <$> d')) (Dom y (getName <$> d'))
        else emit (Dom y (getName <$> d')) (Dom x (getName <$> d'))
      loop (orig d' : ds) p (d', as')
    step ds p (a :=> b) = do
      ds' <- step ds (not p) a
      step ds' p b
    step ds _ _ = return ds

-- Infer constraints for a program expression
infer :: Core.CoreExpr -> InferM Scheme
infer (Core.Var v) =
  case Core.isDataConId_maybe v of
    Just k
      -- Ignore typeclass evidence
      | Core.isClassTyCon $ Core.dataConTyCon k -> return $ Mono Ambiguous
      -- Infer constructor
      | otherwise -> do
        scheme <- fromCoreCons (DataType Initial k)
        case decompTy (body scheme) of
          -- Refinable constructor
          (_, Inj x d _) -> do
            s <- mkCon k
            emit s (Dom x (getName <$> d)) >> return scheme
          -- Unrefinable constructor
          _ -> return scheme
    -- Infer variable
    Nothing -> getVar v
-- Type literal
infer l@(Core.Lit _) = fromCoreScheme $ Core.exprType l
-- Type application
infer (Core.App e1 (Core.Type e2)) = do
  t' <- fromCore e2
  scheme <- infer e1
  case scheme of
    Forall (a : as) t ->
      return $ Forall as (subTyVar a t' t)
    Mono Ambiguous -> return $ Mono Ambiguous
    _ -> pprPanic "Type is already saturated!" (ppr ())
-- Term application
infer (Core.App e1 e2) = infer e1 >>= \case
  Forall as Ambiguous -> Forall as Ambiguous <$ infer e2
  -- TODO: This should raise a warning for as /= []!
  Forall as (t3 :=> t4) -> do
    t2 <- mono <$> infer e2
    inferSubType t2 t3
    return $ Forall as t4
  _ -> pprPanic "Term application to non-function!" $ ppr (Core.exprType e1, Core.exprType e2)
infer (Core.Lam x e)
  | Core.isTyVar x = do
    -- Type abstraction
    a <- getExternalName x
    infer e >>= \case
      Forall as t -> return $ Forall (a : as) t
  | otherwise = do
    -- Variable abstraction
    t1 <- fromCore $ Core.varType x
    putVar (getName x) (Mono t1) (infer e) >>= \case
      Forall as t2 -> return $ Forall as (t1 :=> t2)
-- Local prog
infer (Core.Let b e) = do
  ts <- inferRec False b
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
    Inj rvar d as -> do
      ks <-
        mapMaybeM
          ( \(Core.DataAlt k, xs, rhs) -> do
              reach <- isBranchReachable e k
              if reach
                then do
                  -- Add constructor arguments introduced by the pattern
                  xs_ty <- fst . decompTy <$> fromCoreConsInst (k <$ d) as
                  let ts = M.fromList [(getName x, Mono t) | (x, t) <- zip xs xs_ty]
                  branch e k rvar (level d) $ do
                    -- Constructor arguments are from the same refinement environment
                    mapM_ (\(Mono kti) -> inferSubType (inj rvar kti) kti) ts
                    -- Ensure return type is valid
                    ret_i <- mono <$> putVars ts (infer rhs)
                    inferSubType ret_i ret
                  -- Record constructors
                  return (Just k)
                else return Nothing
          )
          alts'
      case def of
        Nothing -> do
          -- Ensure destructor is total if not nested
          top <- topLevel e
          s <- mkSet ks
          when top $ emit (Dom rvar (getName <$> d)) s
        Just rhs ->
          -- Guard default case by constructors that have not occured
          branchAny e (tyConDataCons (orig d) L.\\ ks) rvar (level d) $ do
            ret_i <- mono <$> infer rhs
            inferSubType ret_i ret
    -- Infer an unrefinable case expression
    Base _ as ->
      forM_ altf $ \case
        (Core.DataAlt k, xs, rhs) -> do
          -- k' <- defaultLevel k
          reach <- isBranchReachable e k
          when reach $ do
            -- Add constructor arguments introduced by the pattern
            xs_ty <- fst . decompTy <$> fromCoreConsInst (DataType Initial k) as
            let ts = M.fromList [(getName x, Mono t) | (x, t) <- zip xs xs_ty]
            -- Ensure return type is valid
            ret_i <- mono <$> putVars ts (infer rhs)
            inferSubType ret_i ret
        (_, _, rhs) -> do
          -- Ensure return type is valid
          ret_i <- mono <$> infer rhs
          inferSubType ret_i ret
    -- Ambiguous
    _ ->
      mapM_
        ( \(_, _, rhs) -> do
            ret_i <- mono <$> infer rhs
            inferSubType ret_i ret
        )
        altf
  return $ Mono ret
-- Track source location
infer (Core.Tick Core.SourceNote {Core.sourceSpan = s} e) = setLoc s $ infer e
-- Ignore other ticks
infer (Core.Tick _ e) = infer e
-- Infer cast
infer (Core.Cast e _) = do
  _ <- infer e
  return (Mono Ambiguous)
-- Cannot infer a coercion expression.
-- For most programs these will never occur outside casts.
infer _ = error "Unimplemented"

mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM op = foldr f (return [])
  where
    f x xs =
      op x >>= \case
        Nothing -> xs
        Just y -> do
          ys <- xs
          return (y : ys)
