module Resolve where

import Context
import Types
import Data.List as L
import Data.Map

resolve :: [(String, ConGraph)] -> [(String, [(Type, Type)])]
resolve = -- reformat 

resolve' :: [(String, [(String, (Map String Type, Map (String, Bool, String) Type))], [(Type, Type)])] -> [(String, [(Type, Type)])]
resolve' cgs = resolve'' cgs xhs
  where
    xhs = fmap (\(x, xsigmas, ts) -> (x, [])) cgs

resolve'' :: [(String, [(String, (Map String Type, Map (String, Bool, String) Type))], [(Type, Type)])] -> [(String, [(Type, Type)])] -> [(String, [(Type, Type)])]
resolve'' cgs xhs = if complete cgs xhs
  then xhs
  else let
    cgs' = fromList $ fmap (\(x, xsigmas, ts) -> (x, ts)) cgs
    xhs' = [(xi, L.union thi (cgs' ! xi)) | (xi, thi) <- xhs]
    in resolve'' [(xi, xsigmas, pushThrough xi xsigmas ts)| (xi, xsigmas, ts) <- cgs] xhs'

complete :: [(String, [(String, (Map String Type, Map (String, Bool, String) Type))], [(Type, Type)])] -> [(String, [(Type, Type)])] -> Bool
complete cgs xhs = let
  cgs' = fromList $ fmap (\(x, xsigmas, ts) -> (x, ts)) cgs
  xhs' = fromList xhs
  in all (\x -> all (\t -> t `elem` (xhs' ! x)) (cgs' ! x)) (keys xhs')

pushThrough :: String -> [(String, (Map String Type, Map (String, Bool, String) Type))] -> [(Type, Type)] -> [(Type, Type)]
pushThrough x xsigmas [] = []
pushThrough x xsigmas (t:ts) = case (fromList xsigmas) !? x of
  Just (tv, rv) -> (sub tv rv t) : (pushThrough x xsigmas ts)
  otherwise -> pushThrough x xsigmas ts
