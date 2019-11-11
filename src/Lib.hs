module Lib
    ( plugin
    ) where

import System.IO

import Control.Monad.RWS

import qualified Data.Map as M
import Binary

import Types
import InferM
import PrettyPrint
import Serialization
import InferCoreExpr

import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoStrictness, CoreDoPluginPass "Constraint Inference" (liftIO. inferGuts)] ++ todo)

inferGuts :: ModGuts -> IO ModGuts
inferGuts guts@ModGuts{mg_binds = p, mg_tcs = tcs, mg_module = m} = do
  -- pprTraceM "" (ppr p)

  -- Infer constraints
  let (tss, _, _) = runRWS (inferProg p) Context{var = M.empty} 0

  -- Display typeschemes
  mapM_ (\(v, ts) -> do
    putStrLn ""
    putStrLn $ showSDocUnsafe $ format v ts
    putStrLn ""
    ) tss

  -- Save typescheme to temporary file
  (fp, h) <- openBinaryTempFile "" "typescheme"
  bh <- openBinMem 1000
  put_ bh tss
  writeBinMem bh fp

  -- Close temporary file
  hClose h
  
  return guts