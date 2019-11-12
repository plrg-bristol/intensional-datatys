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

import Name
import BinIface
import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoStrictness, CoreDoPluginPass "Constraint Inference" (liftIO. inferGuts)] ++ todo)

inferGuts :: ModGuts -> IO ModGuts
inferGuts guts@ModGuts{mg_deps = d, mg_module = m, mg_binds = p} = do
  -- pprTraceM "" (ppr p)

  -- Load modules
  pprTraceM "" (ppr d)

  -- Infer constraints
  let (tss, _, _) = runRWS (inferProg p) Context{var = M.empty} 0

  -- Display typeschemes
  mapM_ (\(v, ts) -> do
    putStrLn ""
    putStrLn $ showSDocUnsafe $ format v ts
    putStrLn ""
    ) tss

  -- TODO: only globalise/serialize export binds
  let tss' = globalise m tss
    
  -- Save typescheme to temporary file
  bh <- openBinMem 1000
  putWithUserData (const $ return ()) bh tss'
  writeBinMem bh $ moduleNameString $ moduleName m
  
  return guts