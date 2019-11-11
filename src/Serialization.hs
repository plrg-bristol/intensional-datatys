{-# LANGUAGE FlexibleInstances, InstanceSigs #-}

module Serialization where

import Binary

import Types

instance Binary Sort where
  put_ bh (SVar a) = do
    put_ bh (1 :: Int)
    put_ bh a
  put_ bh (SData tc as) = do
    put_ bh (2 :: Int)
    put_ bh tc
    put_ bh as
  put_ bh (SArrow s1 s2) =  do
    put_ bh (3 :: Int)
    put_ bh s1
    put_ bh s2
  put_ bh (SApp s1 s2) = do
    put_ bh (4 :: Int)
    put_ bh s1
    put_ bh s2

  get bh = do
    t <- get bh
    case t :: Int of
      0 -> do
        a <- get bh
        return $ SVar a
      2 -> do
        tc <- get bh
        as <- get bh
        return $ SData tc as
      3 -> do
        s1 <- get bh
        s2 <- get bh
        return $ SArrow s1 s2
      4 -> do
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