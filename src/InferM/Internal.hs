{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module InferM.Internal
  ( Flags (..),
    Error (..),
    Context,
    InferM (..),
    runInferM,
    allowContra,
    defaultLevel,
    isUnroll,
    fresh,
    getMod,
    getLoc,
    setLoc,
    topLevel,
    isBranchReachable,
    trivial,
    branch,
    putVar,
    putVars,
    getVar,
  )
where

import ConGraph
import Constraints
import CoreSubst
import CoreSyn (CoreExpr)
import CoreUtils
import qualified Data.Map as M
import qualified Data.Set as S
import DataCon
import FastString
import IfaceType
import Module
import Name
import Outputable hiding (empty)
import Scheme
import SrcLoc hiding (L, getLoc)
import ToIface
import qualified TyCoRep as Tcr
import TyCon
import Type (splitForAllTys)
import Types
import Var
import Prelude hiding (mod)

-- The environment variables and their types
type IContext = M.Map Name (Scheme IfaceTyCon)

type Context = M.Map Name (Scheme TyCon)

-- TODO: add warning level
data Flags = Flags
  { mod :: Module, -- The current module
    contra :: Bool, -- Allow contravariant constructors
    unroll :: Bool -- Unroll datatypes
  }

-- Invalid constraint information
data Error where
  Error :: String -> SrcSpan -> K a -> K b -> Error

-- The inference monad with all the bells and whistles
-- Essentially an unrolled ExceptT RWST
newtype InferM m a = InferM
  { unInferM ::
      Flags -> -- command line flags
      IContext -> -- constrained environment
      SrcSpan -> -- current location
      [(DataType [DataCon], CoreExpr)] -> -- case stack
      Int -> -- fresh
      Int -> -- fresh at last saturation
      ConGraph -> -- constraints
      m (Either Error ([(DataType [DataCon], CoreExpr)], Int, Int, ConGraph, a))
  }

runInferM :: Monad m => InferM m a -> Flags -> IContext -> m (Either Error a)
runInferM m flags g =
  fmap (\(_, _, _, _, a) -> a) <$> unInferM m flags g (UnhelpfulSpan (mkFastString "Top level")) [] 0 0 empty

-- Extract the entire state for breakpoints etc.
debug :: Monad m => InferM m (Flags, IContext, SrcSpan, [(DataType [DataCon], CoreExpr)], Int, Int, ConGraph)
debug = InferM $ \flags gamma loc path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, (flags, gamma, loc, path, fresh, old_fresh, cs))

instance Monad m => Functor (InferM m) where
  fmap f mx = do
    ~x <- mx
    return (f x)
  {-# INLINE fmap #-}

instance Monad m => Applicative (InferM m) where
  pure = return
  {-# INLINE pure #-}

  mf <*> mx = do
    ~f <- mf
    ~x <- mx
    return (f x)
  {-# INLINE (<*>) #-}

instance Monad m => Monad (InferM m) where
  return a = InferM $ \_ _ _ path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, a)
  {-# INLINE return #-}

  m >>= k = InferM $ \flags gamma loc path fresh old_fresh cs -> do
    ~ma <- unInferM m flags gamma loc path fresh old_fresh cs
    case ma of
      Left ~err -> return $ Left err
      Right ~(path', fresh', old_fresh', cs', a) -> unInferM (k a) flags gamma loc path' fresh' old_fresh' cs'
  {-# INLINE (>>=) #-}

-- Extract current module
getMod :: Monad m => InferM m Module
getMod = InferM $ \flags _ _ path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, mod flags)

-- Do the command line flags enable contravariant constructors
allowContra :: Monad m => InferM m Bool
allowContra = InferM $ \flags _ _ path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, contra flags)

-- Extract current src location
getLoc :: Monad m => InferM m SrcSpan
getLoc = InferM $ \_ _ loc path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, loc)

-- Specify a location
setLoc :: SrcSpan -> InferM m a -> InferM m a
setLoc loc m = InferM $ \flags gamma _ -> unInferM m flags gamma loc

-- A unique integer
fresh :: Monad m => InferM m Int
fresh = InferM $ \_ _ _ path fresh old_fresh cs -> return $ Right (path, fresh + 1, old_fresh, cs, fresh)

-- Has the expression already been pattern matched on?
topLevel :: Monad m => CoreExpr -> InferM m Bool
topLevel e = InferM $ \_ _ loc path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, inStack path)
  where
    inStack = foldr (\(_, e') es -> not (cheapEqExpr e e') && es) True

-- Is the branch reachable
isBranchReachable :: Monad m => CoreExpr -> DataType DataCon -> InferM m Bool
isBranchReachable e k = InferM $ \_ _ loc path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, inStack path)
  where
    inStack = foldr (\(ks, e') es -> (not (cheapEqExpr e e') || homoElem k ks) && es) True
    homoElem (Level0 k) (Level0 ks) = k `elem` ks
    homoElem (Level1 k) (Level1 ks) = k `elem` ks
    homoElem _ _ = False

defaultLevel :: Monad m => a -> InferM m (DataType a)
defaultLevel d = InferM $ \flags _ loc path fresh old_fresh cs ->
  if unroll flags
    then return $ Right (path, fresh, old_fresh, cs, Level0 d)
    else return $ Right (path, fresh, old_fresh, cs, Neutral d)

isUnroll :: Monad m => InferM m Bool
isUnroll = InferM $ \flags _ _ path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, unroll flags)

-- Is a datatype unrefinable
trivial :: TyCon -> Bool
trivial = (== 1) . length . tyConDataCons

-- Guard local constraints by a set of possible constructors
branch :: Monad m => Maybe CoreExpr -> DataType [DataCon] -> Int -> InferM m a -> InferM m a
branch me ks x m = InferM $ \flags gamma loc path fresh old_fresh cs -> do
  let d = fmap (dataConTyCon . head) ks
  if trivial (underlying d)
    then fmap (\(_, fresh', old_fresh', cs', a) -> (path, fresh', old_fresh', cs `union` cs', a)) <$> unInferM m flags gamma loc path fresh old_fresh cs
    else
      fmap (\(_, fresh', old_fresh', cs', a) -> (path, fresh', old_fresh', cs `union` guardWith (getName <$> underlying ks) x (getName <$> d) cs', a))
        <$> unInferM m flags gamma loc (case me of Just e -> (ks, e) : path; Nothing -> path) fresh old_fresh cs

-- Insert variables into environment
putVar :: Name -> Scheme TyCon -> InferM m a -> InferM m a
putVar n t m = InferM $ \flags gamma -> unInferM m flags (M.insert n (toIfaceTyCon <$> t) gamma)

putVars :: Context -> InferM m a -> InferM m a
putVars c m = InferM $ \flags gamma -> unInferM m flags (M.union (fmap toIfaceTyCon <$> c) gamma)

-- Lookup constrained variable
getVar :: Monad m => Var -> InferM m (Maybe (Scheme TyCon))
getVar v = InferM $ \_ gamma _ path fresh old_fresh cs -> return $ Right (path, fresh, old_fresh, cs, promote <$> M.lookup (getName v) gamma)
  where
    vty_body :: Tcr.Type
    vty_body = snd $ splitForAllTys $ varType v
    promote :: Scheme IfaceTyCon -> Scheme TyCon
    promote (Scheme bvs tyvs body cs) = Scheme bvs tyvs (promote' vty_body body) cs
    promote' :: Tcr.Type -> Type e IfaceTyCon -> Type e TyCon
    promote' (Tcr.TyConApp tc args) t
      | isTypeSynonymTyCon tc, -- Type synonym
        Just (as, s) <- synTyConDefn_maybe tc =
        promote' (substTy (extendTvSubstList emptySubst (zip as args)) s) t
    promote' _ (Var a) = Var a
    promote' (Tcr.AppTy a' b') (App a b) = App (promote' a' a) (promote' b' b)
    promote' (Tcr.TyConApp tc as') (Data d as) = Data (tc <$ d) (uncurry promote' <$> zip as' as)
    promote' (Tcr.TyConApp tc as') (Inj x d as) = Inj x (tc <$ d) (uncurry promote' <$> zip as' as)
    promote' (Tcr.FunTy a' b') (a :=> b) = promote' a' a :=> promote' b' b
    promote' _ (Lit l) = Lit l
    promote' _ Ambiguous = Ambiguous
    promote' t i = pprPanic "Interface type does not align with term type!" $ ppr (t, i)
