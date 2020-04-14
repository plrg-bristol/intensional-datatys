{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module InferM.Internal (
  Context,
  InferM(..),
  runInferM,
  fresh,
  getMod,
  getLoc,
  setLoc,
  topLevel,
  branch,
  putVar,
  putVars,
  getVar,
) where

import qualified Data.Set as S
import qualified Data.Map as M

import Type (splitForAllTys)
import Name
import TyCon
import Module
import SrcLoc hiding (getLoc)
import DataCon
import Outputable hiding (empty)
import CoreUtils
import Var
import CoreSubst
import CoreSyn (CoreExpr)
import qualified TyCoRep as Tcr
import ToIface
import IfaceType
import FastString

import Types
import Scheme
import ConGraph

-- The environment variables and their types
type IContext = M.Map Name (Scheme IfaceTyCon)
type Context  = M.Map Name (Scheme TyCon)

-- The inference monad with all the bells and whistles
-- Essentially an unrolled RWST
newtype InferM m a = InferM {
  unInferM :: Module     -- current module
           -> IContext   -- constrained environment
           -> SrcSpan    -- current location
           -> [CoreExpr] -- case stack
           -> Int        -- fresh
           -> ConGraph   -- constraints
           -> m ([CoreExpr], Int, ConGraph, a)
}

runInferM :: Monad m => InferM m a -> Module -> IContext -> m a
runInferM m mod g = do
  (_, _, _, a) <- unInferM m mod g (UnhelpfulSpan (mkFastString "Top level")) [] 0 empty
  return a

-- Extract the entire state for breakpoints etc.
debug :: Monad m => InferM m (Module, IContext, SrcSpan, [CoreExpr], Int, ConGraph)
debug = InferM $ \mod gamma loc path fresh cs -> return (path, fresh, cs, (mod, gamma, loc, path, fresh, cs))

instance Functor m => Functor (InferM m) where
    fmap func m = InferM $ \mod gamma loc path fresh cs -> (\(path', fresh', cs', a) -> (path', fresh', cs', func a)) <$> unInferM m mod gamma loc path fresh cs
    {-# INLINE fmap #-}

instance (Functor m, Monad m) => Applicative (InferM m) where
    pure a = InferM $ \_ _ _ path fresh cs -> return (path, fresh, cs, a)
    {-# INLINE pure #-}

    InferM mf <*> InferM mx = InferM $ \mod gamma loc path fresh cs -> do
        (path', fresh', cs', f)   <- mf mod gamma loc path fresh cs
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

-- Has the expression already been pattern matched on?
topLevel :: Monad m => CoreExpr -> InferM m Bool
topLevel e = InferM $ \_ _ loc path fresh cs -> return (path, fresh, cs, inStack path)
  where
    inStack = foldr (\e' es -> not (cheapEqExpr e e') && es) True

-- Guard local constraints by a set of possible constructors
branch :: Monad m => Maybe CoreExpr -> [DataCon] -> Int -> InferM m a -> InferM m a
branch me ks x m = InferM $ \mod gamma loc path fresh cs -> do
  let d = Level0 (dataConTyCon $ head ks)
  (_, fresh', cs', a) <- unInferM m mod gamma loc (case me of { Just e -> e:path; Nothing -> path}) fresh cs
  return (path, fresh', cs `union` guardWith (S.fromList $ getName <$> ks) x (getName <$> d) cs', a)

-- Insert variables into environment
putVar :: Name -> Scheme TyCon -> InferM m a -> InferM m a
putVar n t m = InferM $ \mod gamma -> unInferM m mod (M.insert n (toIfaceTyCon <$> t) gamma)

putVars :: Context -> InferM m a -> InferM m a
putVars c m = InferM $ \mod gamma -> unInferM m mod (M.union (fmap toIfaceTyCon <$> c) gamma)

-- Lookup constrained variable
getVar :: Monad m => Var -> InferM m (Maybe (Scheme TyCon))
getVar v = InferM $ \_ gamma _ path fresh cs -> return (path, fresh, cs, promote <$> M.lookup (getName v) gamma)
  where
    vty_body :: Tcr.Type
    vty_body = snd $ splitForAllTys $ varType v

    promote :: Scheme IfaceTyCon -> Scheme TyCon
    promote (Scheme bvs tyvs body cs) = Scheme bvs tyvs (promote' vty_body body) cs

    promote' :: Tcr.Type -> Type e IfaceTyCon -> Type e TyCon
    promote' (Tcr.TyConApp tc args) t
      | isTypeSynonymTyCon tc  -- Type synonym
      , Just (as, s) <- synTyConDefn_maybe tc    = promote' (substTy (extendTvSubstList emptySubst (zip as args)) s) t
    promote' _ (Var a)                           = Var a
    promote' (Tcr.AppTy a' b') (App a b)         = App (promote' a' a) (promote' b' b)
    promote' (Tcr.TyConApp tc as') (Data d as)   = Data (tc <$ d) (uncurry promote' <$> zip as' as)
    promote' (Tcr.TyConApp tc as') (Inj x d as)  = Inj x (tc <$ d) (uncurry promote' <$> zip as' as)
    promote' (Tcr.FunTy a' b')  (a :=> b)        = promote' a' a :=> promote' b' b
    promote' _ (Lit l)                           = Lit l
    promote' _ Ambiguous                         = Ambiguous
    promote' t i                                 = pprPanic "Interface type does not align with term type!" $ ppr (t, i)
