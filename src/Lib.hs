{-# LANGUAGE BangPatterns #-}

module Lib
    ( plugin
    ) where

import System.IO
import System.Directory

import Control.Monad.RWS hiding (get)

import qualified Data.Map as M
import Binary

import Types
import InferM
import PrettyPrint
import Serialization
import InferCoreExpr

import Name
import IfaceEnv
import BinIface
import GhcPlugins
import TcRnMonad
import TcRnTypes
import IOEnv

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoStrictness, CoreDoPluginPass "Constraint Inference" inferGuts] ++ todo)

interfaceName :: ModuleName -> FilePath
interfaceName = ("interface/" ++) . moduleNameString

inferGuts :: ModGuts -> CoreM ModGuts
-- HscEnv IORef UniqSupply
inferGuts guts@ModGuts{mg_deps = d, mg_module = m, mg_binds = p} = do
  -- pprTraceM "" (ppr p)

  -- Reload saved typeschemes
  deps <- liftIO $ filterM doesFileExist $ map (interfaceName . fst) $ dep_mods d
  hask <- getHscEnv 
  !env  <- liftIO $ initTcRnIf '\0' hask () () $ foldM (\env fp -> do
    bh    <- liftIO $ readBinMem fp
    cache <- mkNameCacheUpdater
    tss   <- liftIO (getWithUserData cache bh :: IO [(Name, TypeScheme)])
    let env' = foldr (\(x, ts) env' -> insertVar x ts env') Context{var = M.empty} tss
    return env') Context{var = M.empty} deps

  -- Infer constraints
  let (tss, _, _) = runRWS (inferProg p) env 0

  -- Display typeschemes
  liftIO $ mapM_ (\(v, ts) -> do
    putStrLn ""
    putStrLn $ showSDocUnsafe $ format v ts
    putStrLn ""
    ) tss

  -- TODO: only globalise/serialize export binds
  let tss' = globalise m tss
    
  -- Save typescheme to temporary file
  exist <- liftIO $ doesDirectoryExist "interface"
  liftIO $ unless exist (createDirectory "interface")
  bh <- liftIO $ openBinMem 1000
  liftIO $ putWithUserData (const $ return ()) bh tss'
  liftIO $ writeBinMem bh $ interfaceName $ moduleName m

  -- TODO: delete files ??  
  return guts