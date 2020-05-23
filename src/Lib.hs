{-# LANGUAGE DataKinds #-}

module Lib
  ( plugin,
  )
where

import BinIface
import Binary
import Control.Monad
import qualified Data.Map as M
import Data.Time
import GhcPlugins
import Guards
import IfaceEnv
import IfaceType
import InferCoreExpr
import InferM
import Scheme
import System.Directory
import TcIface
import TcRnMonad
import ToIface
import TyCoRep
import Prelude hiding (mod)
import IfaceSyn

plugin :: Plugin
plugin = defaultPlugin {pluginRecompile = \_ -> return NoForceRecompile, installCoreToDos = install}
  where
    install cmd todo = return ([CoreDoStrictness, CoreDoPluginPass "Constraint Inference" (inferGuts cmd)] ++ todo)

interfaceName :: ModuleName -> FilePath
interfaceName = ("interface/" ++) . moduleNameString

inferGuts :: [CommandLineOption] -> ModGuts -> CoreM ModGuts
inferGuts cmd guts@ModGuts {mg_deps = d, mg_module = m, mg_binds = p} = do
  start <- liftIO getCurrentTime
  when ("srcDump" `elem` cmd) $ pprTraceM "" (ppr p)

  -- Read command line arguments
  let allowContra = True
  let unrollDataTypes = True

  -- Reload saved typeschemes
  deps <- liftIO $ filterM (doesFileExist . interfaceName) (fst <$> dep_mods d)
  hask <- getHscEnv
  let gbl =
        IfGblEnv
          { if_doc = text "initIfaceLoad",
            if_rec_types = Nothing
          }
  env <-
    liftIO $ initTcRnIf 'i' hask gbl (mkIfLclEnv m empty False) $
      foldM
        ( \env m_name -> do
            bh <- liftIO $ readBinMem $ interfaceName m_name
            cache <- mkNameCacheUpdater
            ictx <- M.fromList <$> liftIO (getWithUserData cache bh)
            ctx <-
              mapM
                ( \(Scheme tyvs dvs ift g) -> do
                    t <- mapM tcIfaceTyCon ift
                    return (Scheme tyvs dvs t g)
                )
                ictx
            return (M.union ctx env)
        )
        M.empty
        deps
  -- Infer constraints
  (gamma, errs) <-
    runInferM
      ( inferProg (dependancySort p)
          >>= mapM (\(Scheme tyvs dvs t g) -> Scheme tyvs dvs (fmap toIfaceTyCon t) <$> mapM (mapM toList) g)
      )
      unrollDataTypes
      allowContra
      m
      env
  -- Display typeschemes
  liftIO
    $ mapM_
      ( \(v, ts) -> do
          putStrLn ""
          putStrLn $ showSDocUnsafe $ ppr (v, ts)
          putStrLn ""
      )
    $ M.toList gamma
  -- Display errors
  liftIO $ mapM_ (putStrLn . showSDocUnsafe . ppr) errs
  -- Save typescheme to temporary file
  exist <- liftIO $ doesDirectoryExist "interface"
  liftIO $ unless exist (createDirectory "interface")
  bh <- liftIO $ openBinMem 1000
  liftIO $ putWithUserData (const $ return ()) bh (M.toList $ M.filterWithKey (\k _ -> isExternalName k) gamma)
  liftIO $ writeBinMem bh $ interfaceName $ moduleName m
  stop <- liftIO getCurrentTime
  when ("time" `elem` cmd) $ do
    liftIO $ print $ diffUTCTime stop start
    liftIO $ print (M.size gamma)
  return guts

tcIfaceTyCon :: IfaceTyCon -> IfL TyCon
tcIfaceTyCon iftc = do
  e <- tcIfaceExpr (IfaceType (IfaceTyConApp iftc IA_Nil))
  case e of
    Type (TyConApp tc _) -> return tc

-- Sort a program in order of dependancies
dependancySort :: CoreProgram -> CoreProgram
dependancySort p = foldl go [] depGraph
  where
    -- Pair binder groups with their dependancies
    depGraph :: [(CoreBind, [CoreBind])]
    depGraph = [(b, [group | rhs <- rhssOfBind b, fv <- exprFreeVarsList rhs, group <- findGroup p fv, bindersOf group /= bindersOf b]) | b <- p]
    go :: [CoreBind] -> (CoreBind, [CoreBind]) -> [CoreBind]
    go [] (b, deps) = deps ++ [b]
    go (b' : bs) (b, deps)
      | bindersOf b == bindersOf b' = deps ++ [b] ++ foldl remove bs deps -- Insert dependencies just before binder
      | otherwise = b' : go bs (b, remove deps b')
    -- Remove duplicates
    remove [] _ = []
    remove (y : ys) x
      | bindersOf x == bindersOf y = ys
      | otherwise = y : remove ys x
    -- Find the group in which the variable is contained
    findGroup :: [CoreBind] -> Var -> [CoreBind]
    findGroup [] _ = []
    findGroup (b : bs) x
      | x `elem` bindersOf b = [b]
      | otherwise = findGroup bs x
