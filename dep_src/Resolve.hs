{-# LANGUAGE ViewPatterns #-}

module Resolve where

import Context
import ConGraph
import Types
import Data.List as L
import Data.Map as M

resolve :: [(String, Type, ConGraph)] -> InferM [(String, Type, [(Type, Type)])]
resolve cgs = mapM (\(x, t, ts) -> do { ts' <- saturate ts; return (x, t, ts')}) $ resolve' cgs'
  where
    cgs' = [(x, t, abstractConstraints cg, concreteConstraints cg) | (x, t, cg) <- cgs]

resolve' :: [(String, Type, [(String, (Map String Type, Map (String, Bool, String) Type))], [(Type, Type)])] -> [(String, Type, [(Type, Type)])]
resolve' cgs = resolve'' cgs xhs
  where
    xhs = fmap (\(x, t, xsigmas, ts) -> (x, t, [])) cgs

resolve'' :: [(String, Type, [(String, (Map String Type, Map (String, Bool, String) Type))], [(Type, Type)])] -> [(String, Type, [(Type, Type)])] -> [(String, Type, [(Type, Type)])]
resolve'' cgs xhs = if complete cgs xhs
  then xhs
  else let
    cgs' = M.fromList $ fmap (\(x, t, xsigmas, ts) -> (x, ts)) cgs
    xhs' = [(xi, t, L.union thi (cgs' ! xi)) | (xi, t, thi) <- xhs]
    in resolve'' [(xi, t, xsigmas, pushThrough xi xsigmas ts)| (xi, t, xsigmas, ts) <- cgs] xhs'

complete :: [(String, Type, [(String, (Map String Type, Map (String, Bool, String) Type))], [(Type, Type)])] -> [(String, Type, [(Type, Type)])] -> Bool
complete cgs xhs = let
  cgs' = M.fromList $ fmap (\(x, xsigmas, ts) -> (x, ts)) (ignoreType2 cgs)
  xhs' = M.fromList (ignoreType xhs)
  in all (\x -> all (\t -> t `elem` (xhs' ! x)) (cgs' ! x)) (keys xhs')

pushThrough :: String -> [(String, (Map String Type, Map (String, Bool, String) Type))] -> [(Type, Type)] -> [(Type, Type)]
pushThrough x xsigmas [] = []
pushThrough x xsigmas (t:ts) = case (M.fromList xsigmas) !? x of
  Just (tv, rv) -> (sub tv rv t) : (pushThrough x xsigmas ts)
  otherwise -> pushThrough x xsigmas ts

ignoreType :: [(String, Type, a)] -> [(String, a)]
ignoreType = fmap (\(s, t, a) -> (s, a))

ignoreType2 :: [(String, Type, a, b)] -> [(String, a, b)]
ignoreType2 = fmap (\(s, t, a, b) -> (s, a, b))
