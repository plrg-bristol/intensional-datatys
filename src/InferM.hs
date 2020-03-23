{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}

module InferM (
  Context,
  getExternalName,
  emitConDom,
  emitDomSet,
  InferM,
  runInferM,
  getMod,
  getLoc,
  setLoc,
  topLevel,
  fresh,
  branch,
  debug,
  putVar,
  putVars,
  getVar,
  fromCore,
  fromCoreScheme,
  emitSetCon,
  emitTyCon,
  saturate,
) where

import Control.Monad hiding (guard)
import qualified Data.Set as S
import qualified Data.Map as M

import Types
import Scheme
import Guard
import ConGraph

import Var
import Name
import TyCon
import Module
import ToIface
import DataCon
import CoreSubst
import CoreUtils
import IfaceType
import UniqSet
import FastString
import SrcLoc hiding (getLoc)
import Outputable hiding (empty)
import qualified TyCoRep as Tcr
import qualified CoreSyn as Core

-- The environment variables and their types
type IContext c = M.Map Name (Scheme T IfaceTyCon c)
type Context c = M.Map Name (Scheme T TyCon c)

-- The inference monad with all the bells and whistles
-- Essentially an unrolled RWST
newtype InferM m a = InferM {
  unInferM :: Module            -- current module
           -> IContext ConGraph -- constrained environment
           -> SrcSpan           -- current location
           -> [Core.CoreExpr]   -- case stack
           -> Int               -- fresh
           -> ConGraph          -- constraints
           -> m ([Core.CoreExpr], Int, ConGraph, a)
}

runInferM :: Monad m => InferM m a -> Module -> IContext ConGraph -> m a
runInferM m mod g = do
  (_, _, _, a) <- unInferM m mod g (UnhelpfulSpan (mkFastString "Top level")) [] 0 empty
  return a

-- Extract the entire state for breakpoints etc.
debug :: Monad m => InferM m (Module, IContext ConGraph, SrcSpan, [Core.CoreExpr], Int, ConGraph)
debug = InferM $ \mod gamma loc path fresh cs -> return (path, fresh, cs, (mod, gamma, loc, path, fresh, cs))

instance Functor m => Functor (InferM m) where
    fmap func m = InferM $ \mod gamma loc path fresh cs -> (\(path', fresh', cs', a) -> (path', fresh', cs', func a)) <$> unInferM m mod gamma loc path fresh cs
    {-# INLINE fmap #-}

instance (Functor m, Monad m) => Applicative (InferM m) where
    pure a = InferM $ \_ _ _ path fresh cs -> return (path, fresh, cs, a)
    {-# INLINE pure #-}

    InferM mf <*> InferM mx = InferM $ \mod gamma loc path fresh cs -> do
        (path', fresh',  cs', f)   <- mf mod gamma loc path fresh cs
        (path'', fresh'', cs'', a) <- mx mod gamma loc path' fresh' cs'
        return (path'', fresh'', cs'', f a)
    {-# INLINE (<*>) #-}

instance Monad m => Monad (InferM m) where
    return a = InferM $ \_ _ _ path fresh cs -> return (path, fresh, cs, a)
    {-# INLINE return #-}

    m >>= k = InferM $ \mod gamma loc path fresh cs -> do
        ~(path', fresh', cs', a)    <- unInferM m mod gamma loc path fresh cs
        ~(path'', fresh'', cs'', b) <- unInferM (k a) mod gamma loc path' fresh' cs'
        return (path'', fresh'', cs'', b)
    {-# INLINE (>>=) #-}

-- Extract current module
getMod :: Monad m => InferM m Module
getMod = InferM $ \mod _ _ path fresh cs -> return (path, fresh, cs, mod)

-- Extract current src location
getLoc :: Monad m => InferM m SrcSpan
getLoc = InferM $ \_ _ loc path fresh cs -> return (path, fresh, cs, loc)

-- Specify a location
setLoc :: SrcSpan -> InferM m a -> InferM m a
setLoc loc m = InferM $ \mod gamma _ -> unInferM m mod gamma loc

-- A unique integer
fresh :: Monad m => InferM m Int
fresh = InferM $ \_ _ _ path fresh cs -> return (path, fresh + 1, cs, fresh)

-- Has the variable already been pattern matched on?
topLevel :: Monad m => Core.CoreExpr -> InferM m Bool
topLevel e = InferM $ \_ _ loc path fresh cs -> return (path, fresh, cs, inStack path)
  where
    inStack = foldr (\e' es -> not (cheapEqExpr e e') && es) True

-- Guard local constraints by a set of possible constructors
branch :: Monad m => Core.CoreExpr -> [DataCon] -> Int -> TyCon -> InferM m a -> InferM m a
branch e ks x d m = InferM $ \mod gamma loc path fresh cs -> do
  (_, fresh', cs', a) <- unInferM m mod gamma loc (e:path) fresh cs
  return (path, fresh', cs `union` guard (S.fromList $ getName <$> ks) x (getName d) cs', a)

-- Upgrade unconstrained scheme
class Constraints c where
  def :: Scheme T TyCon c -> Scheme T IfaceTyCon ConGraph

instance Constraints () where
  def Scheme{ tyvars = as, body = b } = Scheme { tyvars = as, body = toIfaceTyCon <$> b, constraints = empty }

instance Constraints ConGraph where
  def Scheme{ tyvars = as, body = b, constraints = c } = Scheme { tyvars = as, body = toIfaceTyCon <$> b, constraints = c }

-- Insert variables into environment
putVar :: Constraints c => Name -> Scheme T TyCon c -> InferM m a -> InferM m a
putVar n t m = InferM $ \mod gamma -> unInferM m mod (M.insert n (def t) gamma)

putVars :: Constraints c => Context c -> InferM m a -> InferM m a
putVars c m = InferM $ \mod gamma -> unInferM m mod (M.union (def <$> c) gamma)

getConstrainedVar :: Monad m => Name -> InferM m (Maybe (Scheme T IfaceTyCon ConGraph))
getConstrainedVar v = InferM $ \_ gamma _ path fresh cs -> return (path, fresh, cs, M.lookup v gamma)

-- Extract a variable from the environment
getVar :: Monad m => Var -> InferM m (Scheme T TyCon ())
getVar v = do
  var_scheme <- fromCoreScheme $ varType v
  may_scheme <- getConstrainedVar $ getName v
  case may_scheme of
    Just scheme -> do
      -- Localise constraints
      fre_scheme <- foldM (\s x -> liftM2 (rename x) fresh $ return s) scheme (domain $ constraints $ scheme)
      emit (constraints fre_scheme)
      emitIfaceTyCon' (body fre_scheme) (body var_scheme)

    Nothing ->
      -- Maximise library type
      case decomp (body var_scheme) of
        (_, Inj x d _) -> do
          let Tcr.TyConApp d' _ = coreDecomp $ varType v
          l <- getLoc
          mapM_ (\k -> emitSetCon (con (getName k) l) (Dom x $ getName d')) $ tyConDataCons d'
        _ -> return ()
  return var_scheme

-- Get the body/result of a core scheme
coreDecomp :: Tcr.Type -> Tcr.Type
coreDecomp (Tcr.ForAllTy _ t) = coreDecomp t
coreDecomp (Tcr.FunTy _ t)    = coreDecomp t
coreDecomp t                  = t

-- Convert a core datatype
class DataType (e :: Extended) where
  datatype :: Monad m => TyCon -> [Type e TyCon] -> InferM m (Type e TyCon)

instance DataType S where
  datatype d as = return $ Data d as

instance DataType T where
  datatype d as = do
    x <- fresh
    return $ Inj x d as

-- Check whether a core datatype is refinable
refinable :: TyCon -> Bool
refinable tc = (length (tyConDataCons tc) > 1) && all pos (concatMap dataConOrigArgTys $ tyConDataCons tc)
  where
    pos :: Tcr.Type -> Bool
    pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
    pos _                 = True

    neg :: Tcr.Type -> Bool
    neg (Tcr.TyConApp _ _) = False -- Could this test whether tc' is refinable?
    neg (Tcr.TyVarTy _)    = False
    neg (Tcr.FunTy t1 t2)  = pos t1 && neg t2
    neg _                  = True

-- Prepare name for interface
getExternalName :: (Monad m, NamedThing a) => a -> InferM m Name
getExternalName a = do
  let n = getName a
  mod <- getMod
  return $ mkExternalName (nameUnique n) mod (nameOccName n) (nameSrcSpan n)

-- Convert a monomorphic core type
fromCore :: (DataType e, Monad m) => Tcr.Type -> InferM m (Type e TyCon)
fromCore (Tcr.TyVarTy a) = Var <$> getExternalName a
fromCore (Tcr.AppTy t1 t2)   = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return $ App s1 s2
fromCore (Tcr.TyConApp tc args)
  | isTypeSynonymTyCon tc  -- Type synonym
  , Just (as, u) <- synTyConDefn_maybe tc
    = fromCore (substTy (extendTvSubstList emptySubst (zip as args)) u)
  | refinable tc
    = do
        args' <- mapM fromCore args
        datatype tc args'
  | otherwise
    = do
        args' <- mapM fromCore args
        return $ Base tc args'
fromCore (Tcr.FunTy t1 t2) = do
  s1 <- fromCore t1
  s2 <- fromCore t2
  return (s1 :=> s2)
fromCore (Tcr.LitTy l)      = return $ Lit $ toIfaceTyLit l
fromCore (Tcr.ForAllTy a t) = pprPanic "Unexpected polymorphic type!" $ ppr $ Tcr.ForAllTy a t
fromCore t                  = pprPanic "Unexpected cast or coercion type!" $ ppr t

-- Convert a polymorphic core type
fromCoreScheme :: (DataType e, Monad m) => Tcr.Type -> InferM m (Scheme e TyCon ())
fromCoreScheme (Tcr.ForAllTy b t) = do
  let a = getName $ Tcr.binderVar b
  scheme <- fromCoreScheme t
  return scheme{ tyvars = a : tyvars scheme }
fromCoreScheme (Tcr.FunTy t1 t2) = do
  s1     <- fromCore t1
  scheme <- fromCoreScheme t2 -- Is this safe??
  return scheme{ body = s1 :=> body scheme }
fromCoreScheme (Tcr.CastTy t k)   = pprPanic "Unexpected cast type!" $ ppr (t, k)
fromCoreScheme (Tcr.CoercionTy g) = pprPanic "Unexpected coercion type!" $ ppr g
fromCoreScheme t                  = Mono <$> fromCore t

emit :: Monad m => ConGraph -> InferM m ()
emit cg = InferM $ \_ _ _ p f cs -> return (p, f, cg `union` cs, ())

-- Emit a single set constraint
emitSetCon :: Monad m => K -> K -> InferM m ()
emitSetCon k1 k2 =
  case singleton k1 k2 of
    Just cg -> InferM $ \_ _ _ path fresh cs -> return (path, fresh, cg `union` cs, ())
    Nothing -> do
      l <- getLoc
      pprPanic "Invalid set constraint!" $ ppr (k1, k2, l)

emitConDom :: Monad m => DataCon -> Int -> TyCon -> InferM m ()
emitConDom k x d = do
  l <- getLoc
  emitSetCon (con (getName k) l) (Dom x $ getName d)

emitDomSet :: Monad m => Int -> TyCon -> [DataCon] -> InferM m ()
emitDomSet x d ks = do
  l <- getLoc
  emitSetCon (Dom x $ getName d) (Set (mkUniqSet (getName <$> ks)) l)

-- Convert a subtyping constraint to a constraint set and emit
emitTyCon :: Monad m => Type T TyCon -> Type T TyCon -> InferM m ()
emitTyCon (Var _) (Var _)        = return ()
emitTyCon Ambiguous _            = return ()
emitTyCon _ Ambiguous            = return ()
emitTyCon t1 t2
  | shape t1 /= shape t2 = do
    l <- getLoc
    pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
emitTyCon (t11 :=> t12) (t21 :=> t22) =
    emitTyCon t21 t11 >> emitTyCon t12 t22
emitTyCon (Inj x d as) (Inj y _ as')
  | x /= y = do
    mapM_ (\d' -> emitSetCon (Dom x (getName d')) (Dom y (getName d'))) $ slice [d]
    mapM_ (uncurry emitTyCon) $ zip as as'
emitTyCon _ _ = return ()

-- Emit a constraint between interface types
emitIfaceTyCon :: Monad m => Type T TyCon -> Type T IfaceTyCon -> InferM m ()
emitIfaceTyCon (Var _) (Var _)        = return ()
emitIfaceTyCon Ambiguous _            = return ()
emitIfaceTyCon _ Ambiguous            = return ()
emitIfaceTyCon t1 t2
  | shape (toIfaceTyCon <$> t1) /= shape t2 = do
    l <- getLoc
    pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
emitIfaceTyCon (t11 :=> t12) (t21 :=> t22) =
    emitIfaceTyCon' t21 t11 >> emitIfaceTyCon t12 t22
emitIfaceTyCon (Inj x d as) (Inj y _ as')
  | x /= y = do
    mapM_ (\d' -> emitSetCon (Dom x (getName d')) (Dom y (getName d'))) $ slice [d]
    mapM_ (uncurry emitIfaceTyCon) $ zip as as'
emitIfaceTyCon _ _ = return ()

emitIfaceTyCon' :: Monad m => Type T IfaceTyCon -> Type T TyCon -> InferM m ()
emitIfaceTyCon' (Var _) (Var _)        = return ()
emitIfaceTyCon' Ambiguous _            = return ()
emitIfaceTyCon' _ Ambiguous            = return ()
emitIfaceTyCon' t1 t2
  | shape t1 /= shape (toIfaceTyCon <$> t2) = do
    l <- getLoc
    pprPanic "Types must refine the same sort!" $ ppr (t1, t2, l)
emitIfaceTyCon' (t11 :=> t12) (t21 :=> t22) =
    emitIfaceTyCon t21 t11 >> emitIfaceTyCon' t12 t22
emitIfaceTyCon' (Inj x _ as) (Inj y d as')
  | x /= y = do
    mapM_ (\d' -> emitSetCon (Dom x (getName d')) (Dom y (getName d'))) $ slice [d]
    mapM_ (uncurry emitIfaceTyCon') $ zip as as'
emitIfaceTyCon' _ _ = return ()

-- Take the slice of a datatype
slice :: [TyCon] -> [TyCon]
slice tcs
  | tcs' == tcs = tcs
  | otherwise   = slice tcs'
  where
    tcs' = [tc' | tc <- tcs
                , dc <- tyConDataCons tc
                , (Tcr.TyConApp tc' _) <- dataConOrigArgTys dc
                , tc' `notElem` tcs
                , refinable tc']
                ++ tcs

-- Transitively remove local constraints and attach them to variables
saturate :: Monad m => InferM m (Context ()) -> InferM m (Context ConGraph)
saturate m = InferM $ \mod gamma occ_l path fresh cs -> do
  (path', fresh', cs', ts) <- unInferM m mod gamma occ_l path fresh cs
  pprTraceM "Graph:" $ ppr cs'
  case restrict (domain ts) cs' of
    Right i -> return (path', fresh', cs, fmap (\s -> Scheme { tyvars = tyvars s, body = body s, constraints = i }) ts)
    Left (Set k left_l, Set k' right_l) -> pprPanic "Unsatisfiable constraint!" $ ppr (k, k', left_l, right_l, occ_l)
