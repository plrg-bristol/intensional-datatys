{-# LANGUAGE DataKinds #-}
{-# LANGUAGE BangPatterns #-}

module Lib
    ( plugin
    ) where

import Control.Monad

import System.Directory

import Data.Time
import qualified Data.Map as M

import GhcPlugins
import Binary
import BinIface
import IfaceEnv
import TcRnMonad
import IfaceType

import Types
import Scheme
import ConGraph
import InferM
import InferCoreExpr

data Flags = Flags {
  time    :: Bool,
  srcDump :: Bool
}

-- Build flags from command line
mkFlags :: [CommandLineOption] -> Flags
mkFlags cmd = Flags { time = "time" `elem` cmd, srcDump = "srcDump" `elem` cmd }

plugin :: Plugin
plugin = defaultPlugin { pluginRecompile = \_ -> return NoForceRecompile, installCoreToDos = install }
  where
    install cmd todo = return ([CoreDoStrictness, CoreDoPluginPass "Constraint Inference" (inferGuts (mkFlags cmd))] ++ todo)

interfaceName :: ModuleName -> FilePath
interfaceName = ("interface/" ++) . moduleNameString

inferGuts :: Flags -> ModGuts -> CoreM ModGuts
inferGuts flags guts@ModGuts{mg_deps = d, mg_module = m, mg_binds = p} = do

  start <- liftIO getCurrentTime
  when (srcDump flags) $ pprTraceM "" (ppr p)

  -- Reload saved typeschemes
  deps <- liftIO $ filterM (doesFileExist . interfaceName) (fst <$> dep_mods d)
  hask <- getHscEnv
  env  <- liftIO $ initTcRnIf '\0' hask () () $ foldM (\env m_name -> do
    bh    <- liftIO $ readBinMem $ interfaceName m_name
    cache <- mkNameCacheUpdater
    tss   <- liftIO (getWithUserData cache bh :: IO [(Name, Scheme IfaceTyCon)])
    return $ foldr (\(x, ts) env' -> M.insert x ts env') env tss
    ) M.empty deps

  -- Infer constraints
  tss <- runInferM (inferProg $ dependancySort p) m env

  -- Display typeschemes
  liftIO $ mapM_ (\(v, ts) -> do
      putStrLn ""
      putStrLn $ showSDocUnsafe $ ppr (v, ts)
      putStrLn ""
    ) $ M.toList tss

  -- Save typescheme to temporary file
  exist <- liftIO $ doesDirectoryExist "interface"
  liftIO $ unless exist (createDirectory "interface")
  bh <- liftIO $ openBinMem 1000
  liftIO $ putWithUserData (const $ return ()) bh (M.toList $ M.filterWithKey (\k _ -> isExternalName k) tss)
  liftIO $ writeBinMem bh $ interfaceName $ moduleName m

  stop <- liftIO getCurrentTime
  when (time flags) $ liftIO $ print $ diffUTCTime stop start

  return guts

-- Sort a program in order of dependancies
dependancySort :: CoreProgram -> CoreProgram
dependancySort p = foldl go [] depGraph
   where
    -- Pair binder groups with their dependancies
    depGraph :: [(CoreBind, [CoreBind])]
    depGraph = [(b, [group | rhs <- rhssOfBind b, fv <- exprFreeVarsList rhs, group <- findGroup p fv, bindersOf group /= bindersOf b]) | b <- p]

    go :: [CoreBind] -> (CoreBind, [CoreBind]) -> [CoreBind]
    go [] (b, deps)     = deps ++ [b]
    go (b':bs) (b, deps)
      | bindersOf b == bindersOf b'   = deps ++ [b] ++ foldl remove bs deps -- Insert dependencies just before binder
      | otherwise                     = b' : go bs (b, remove deps b')

    -- Remove duplicates
    remove [] _     = []
    remove (y:ys) x
      | bindersOf x == bindersOf y = ys
      | otherwise                  = y : remove ys x

    -- Find the group in which the variable is contained
    findGroup :: [CoreBind] -> Var -> [CoreBind]
    findGroup [] _ = []
    findGroup (b:bs) x
      | x `elem` bindersOf b = [b]
      | otherwise = findGroup bs x
