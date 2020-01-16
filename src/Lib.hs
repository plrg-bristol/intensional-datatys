{-# LANGUAGE BangPatterns #-}

module Lib
    ( plugin
    ) where

import qualified Data.Map as M

import GhcPlugins

import InferM
import InferCoreExpr

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoStrictness, CoreDoPluginPass "Constraint Inference" inferGuts] ++ todo)

-- interfaceName :: ModuleName -> FilePath
-- interfaceName = ("interface/" ++) . moduleNameString

inferGuts :: ModGuts -> CoreM ModGuts
inferGuts guts@ModGuts{mg_deps = d, mg_module = m, mg_binds = p} = do

  -- !start <- liftIO $ getCurrentTime
  -- !() <- pprTraceM "Mod name: " (ppr m)
  -- !() <- pprTraceM "Def count" $ (ppr $ length $ concatMap (\b -> getName <$> (filter (not . isPredTy . varType) $ bindersOf b)) p)

  -- pprTraceM "" (ppr p)

  -- Reload saved typeschemes
  -- deps <- liftIO $ filterM (doesFileExist . interfaceName) (fst <$> dep_mods d)
  -- hask <- getHscEnv 
  -- env  <- liftIO $ initTcRnIf '\0' hask () () $ foldM (\env m -> do
  --   bh    <- liftIO $ readBinMem $ interfaceName m
  --   cache <- mkNameCacheUpdater
  --   tss   <- liftIO (getWithUserData cache bh :: IO [(Name, TypeScheme)])
  --   let tss' = [(n, tagSumsWith m ts) | (n, ts) <- tss]
  --   return $ foldr (\(x, ts) env' -> insertVar x ts env') env tss'
  --   ) M.empty deps

  -- Infer constraints
  tss <- runInferM (inferProg $ dependancySort p) M.empty

  -- Display typeschemes
  liftIO $ mapM_ (\(v, ts) -> do
      putStrLn ""
      putStrLn $ showSDocUnsafe $ ppr (v, ts)
      putStrLn ""
    ) $ M.toList tss

  -- let tss' = globalise m tss
    
  -- -- Save typescheme to temporary file
  -- exist <- liftIO $ doesDirectoryExist "interface"
  -- liftIO $ unless exist (createDirectory "interface")
  -- bh <- liftIO $ openBinMem 1000
  -- liftIO $ putWithUserData (const $ return ()) bh tss'
  -- liftIO $ writeBinMem bh $ interfaceName $ moduleName m

  -- stop <- liftIO $ getCurrentTime
  -- liftIO $ print $ diffUTCTime stop start

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
      | bindersOf b == bindersOf b'   = deps ++ [b] ++ (foldl remove bs deps) -- Insert dependencies just before binder
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
