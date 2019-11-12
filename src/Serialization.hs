{-# LANGUAGE FlexibleInstances, InstanceSigs #-}

module Serialization (
  globalise
) where

import Name
import Binary
import GhcPlugins hiding (Type, Var, App, DataCon)

import Types
import PrettyPrint

instance Binary Sort where
  put_ bh (SVar a) = do
    put_ bh (0 :: Int)
    put_ bh a
  put_ bh (SData tc as) = do
    put_ bh (1 :: Int)
    put_ bh tc
    put_ bh as
  put_ bh (SArrow s1 s2) =  do
    put_ bh (2 :: Int)
    put_ bh s1
    put_ bh s2
  put_ bh (SApp s1 s2) = do
    put_ bh (3 :: Int)
    put_ bh s1
    put_ bh s2

  get bh = do
    t <- get bh
    case t :: Int of
      0 -> do
        a <- get bh
        return $ SVar a
      1 -> do
        tc <- get bh
        as <- get bh
        return $ SData tc as
      2 -> do
        s1 <- get bh
        s2 <- get bh
        return $ SArrow s1 s2
      3 -> do
        s1 <- get bh
        s2 <- get bh
        return $ SApp s1 s2

instance Binary RVar where
  put_ bh (RVar (i, b, tc, as)) = do
    put_ bh i
    put_ bh b
    put_ bh tc
    put_ bh as
    
  get bh = do
    i  <- get bh
    b  <- get bh
    tc <- get bh
    as <- get bh
    return $ RVar (i, b, tc, as)

instance Binary DataCon where
  put_ bh (DataCon (n, as, args)) = do
    put_ bh n
    put_ bh as
    put_ bh args
  
  get bh = do
    n    <- get bh
    as   <- get bh
    args <- get bh
    return $ DataCon (n, as, args)

instance Binary Type where
  put_ bh (Var rv) = do
    put_ bh (0 :: Int)
    put_ bh rv
  put_ bh (Sum _ tc as cs) = do
    put_ bh (1 :: Int)
    put_ bh tc
    put_ bh as
    put_ bh cs
  put_ bh Dot = do
    put_ bh (2 :: Int)
  put_ bh (TVar a) = do
    put_ bh (3 :: Int)
    put_ bh a
  put_ bh (t1 :=> t2) =  do
    put_ bh (4 :: Int)
    put_ bh t1
    put_ bh t2
  put_ bh (App t1 s2) = do
    put_ bh (5 :: Int)
    put_ bh t1
    put_ bh s2

  get bh = do
    t <- get bh
    case t :: Int of
      0 -> do
        rv <- get bh
        return $ Var rv
      1 -> do
        -- e  <- get bh
        tc <- get bh
        as <- get bh
        cs <- get bh
        return $ Sum undefined {- e -} tc as cs
      2 -> return Dot
      3 -> do
        a <- get bh
        return $ TVar a
      4 -> do
        t1 <- get bh
        t2 <- get bh
        return $ t1 :=> t2
      5 -> do
        t1 <- get bh
        s2 <- get bh
        return $ App t1 s2

instance Binary TypeScheme where
  put_ bh (Forall tvs rvs cs u) = do
    put_ bh tvs
    put_ bh rvs
    put_ bh cs
    put_ bh u
  get bh = 
    do
      tvs <- get bh
      rvs <- get bh
      cs  <- get bh
      u   <- get bh
      return $ Forall tvs rvs cs u
  
-- Globalise a bind ready to serialize
globalise :: Module -> [(Name, TypeScheme)] -> [(Name, TypeScheme)]
globalise m binds = zip names' (globaliseTypeScheme m names names' <$> types)
    where
      names  = fst <$> binds
      types  = snd <$> binds
      names' = globaliseName m <$> names

-- Convert local name into globl name
globaliseName :: Module -> Name -> Name
globaliseName _ n | isExternalName n = n
globaliseName m n = mkExternalName (nameUnique n) m (nameOccName n) (nameSrcSpan n)

-- Convert local names in a typescheme to global names
globaliseTypeScheme :: Module -> [Name] -> [Name] -> TypeScheme -> TypeScheme
globaliseTypeScheme m old new (Forall ns xs cs u) = Forall ns' (subNames m old' new' xs) (subNames m old' new' cs) (subNames m old' new' u)
    where
      old' = old ++ ns
      new' = new ++ ns' 
      ns' = globaliseName m <$> ns
  
class NameSub a where
  subName :: Module -> Name -> Name -> a -> a

subNames :: NameSub a => Module -> [Name] -> [Name] -> a -> a
subNames _ [] [] = id
subNames m (n:ns) (n':ns') = subName m n n' . subNames m ns ns'

instance NameSub RVar where
  {-# SPECIALIZE instance NameSub RVar #-}
  subName m n n' (RVar (i, p, tc, ss)) = RVar (i, p, tc, subName m n n' ss)

instance NameSub Sort where
  {-# SPECIALIZE instance NameSub Sort #-}
  subName m n n' (SVar n'')     = SVar $ subName m n n' n''
  subName m n n' (SData tc ss)  = SData tc (subName m n n' ss)
  subName m n n' (SArrow s1 s2) = SArrow (subName m n n' s1) (subName m n n' s2)
  subName m n n' (SApp s1 s2)   = SApp (subName m n n' s1) (subName m n n' s2)

instance NameSub Type where
  {-# SPECIALIZE instance NameSub Type #-}
  subName m n n' (Var r)          = Var $ subName m n n' r
  subName m n n' (Sum e tc ss cs) = Sum e tc (subName m n n' ss) (subName m n n' cs)
  subName _ _ _ Dot               = Dot
  subName m n n' (TVar n'')       = TVar $ subName m n n' n''
  subName m n n' (t1 :=> t2)      = (subName m n n' t1) :=> (subName m n n' t2)
  subName m n n' (App t1 s2)      = App (subName m n n' t1) (subName m n n' s2)

instance NameSub Name where
  subName _ x y x'
    | x == x'   = y
    | otherwise = x'

instance NameSub DataCon where
  {-# SPECIALIZE instance NameSub DataCon #-}
  subName m n n' (DataCon (n'', ns, ss)) = DataCon (subName m n n' n'', ns', subNames m (n:ns) (n':ns') ss)
    where
      ns' = globaliseName m <$> ns

instance (NameSub a, NameSub b) => NameSub (a, b) where
  subName m n n' (a, b) = (subName m n n' a, subName m n n' b)
  
instance NameSub a => NameSub [a] where
  subName m n n' = fmap $ subName m n n'