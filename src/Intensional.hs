{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ViewPatterns #-}

module Intensional (plugin, Benchmark(..)) where

import BinIface
import Binary
import Intensional.Constructors
import Intensional.Constraints
import Intensional.Types
import Control.Monad
import Data.Aeson
import qualified Data.Map as Map
import qualified Data.List as List
import GhcPlugins
import IfaceEnv
import IfaceSyn
import Intensional.InferCoreExpr
import Intensional.InferM
import System.CPUTime
import System.Directory
import TcIface
import TcRnMonad
import ToIface
import TyCoRep
import PprColour
import Pretty (Mode(..))
import OccName
import NameCache (OrigNameCache)
import GHC.Generics (Generic)
import System.IO
import qualified System.Console.Haskeline as Haskeline

{-|
  The GHC plugin is hardwired as @plugin@.  
-}
plugin :: Plugin
plugin = 
    defaultPlugin {
      pluginRecompile = recomp, 
      installCoreToDos = install
    }
  where
    recomp cmd =
      return $ if "force" `elem` cmd then ForceRecompile else NoForceRecompile 
    todoPrefix cmd = [ 
        CoreDoStrictness, -- it is useful to know what is bottom for the purpose of pattern failures
        CoreDoPluginPass "Intensional" (inferGuts cmd)
      ]
    install cmd todo = return (todoPrefix cmd ++ todo)

{-|
    Given a module name @m@, @interfaceName m@ is the file path
    that will be written with the corresponding serialised typings.
-}
interfaceName :: ModuleName -> FilePath
interfaceName = ("interface/" ++) . moduleNameString

inferGuts :: [CommandLineOption] -> ModGuts -> CoreM ModGuts
inferGuts cmd guts@ModGuts {mg_deps = d, mg_module = m, mg_binds = p} = do
  when ("debug-core" `elem` cmd) $ pprTraceM "Core Source:" $ ppr p
  hask <- getHscEnv
  che <- getOrigNameCache 
  dflags <- getDynFlags 
  liftIO $ do
    -- Reload saved typeschemes
    let gbl =
          IfGblEnv { 
            if_doc = text "initIfaceLoad",
            if_rec_types = Nothing
          }
    env <- 
      initTcRnIf 'i' hask gbl (mkIfLclEnv m empty False) $ do
        cache <- mkNameCacheUpdater
        foldM
          ( \env (interfaceName -> m_name, _) -> do
              exists <- liftIO $ doesFileExist m_name
              if exists
                then do
                  bh <- liftIO $ readBinMem m_name
                  ictx <- liftIO $ Map.fromList <$> getWithUserData cache bh
                  ctx <- mapM (mapM tcIfaceTyCon) ictx
                  return (Map.union ctx env)
                else return env
          )
          Map.empty
          (dep_mods d)
    t0 <- getCPUTime
    -- Infer constraints
    let (!gamma, !errs, !stats) = runInferM (inferProg p) m env
    t1 <- getCPUTime
    when ("time" `elem` cmd) $
      recordBenchmarks (moduleNameString (moduleName m)) (t0, t1) stats
    -- Display type errors
    let printErrLn = 
          printSDocLn PageMode dflags stderr (setStyleColoured True $ defaultErrStyle dflags)
    mapM_ (\a -> when (m == modInfo a) $ printErrLn (showTypeError a)) errs
    -- Save typeschemes to interface file
    when (moduleNameString (moduleName m) `elem` cmd) $ 
      repl (gamma Prelude.<> env) m p che
    exist <- doesDirectoryExist "interface"
    unless exist (createDirectory "interface")
    bh <- openBinMem (1024 * 1024)
    putWithUserData
      (const $ return ())
      bh
      (Map.toList $ Map.filterWithKey (\k _ -> isExternalName k) (fmap toIfaceTyCon <$> gamma))
    writeBinMem bh (interfaceName (moduleName m))
    return guts

{-|
  When @cx@ is the type bindings for all the program so far and @md@
  is the currently processed module and @ch@ is GHC's name cache,
  @repl cx md ch@ is a read-eval-print-loop IO action, allowing the 
  user to inspect individual type bindings and output the raw core.
-}
repl :: Context -> Module -> CoreProgram -> OrigNameCache -> IO ()
repl cx md pr ch =
  Haskeline.runInputT Haskeline.defaultSettings loop
  where
    loop = 
      do  mbInput <- Haskeline.getInputLine (modn ++ "> ") 
          case words <$> mbInput of
            Just [":q"]          -> return ()
            Just [":c", strName] -> 
              do  case mkName strName of
                    Just n | Just e <- List.lookup n (map (\(x,y) -> (getName x, y)) $ flattenBinds pr) ->
                      Haskeline.outputStrLn $ showSDocUnsafe $ ppr e
                    _   -> return ()
                  loop
            Just [":t", strName] ->
              do  case mkName strName of
                    Just n | Just ts <- Map.lookup n cx -> 
                      Haskeline.outputStrLn $ showSDocUnsafe $ typingDoc n ts
                    _                                    -> return ()
                  loop
            _              -> loop
    typingDoc n ts = ppr n <+> colon <+> prpr (const empty) ts 
    modn = moduleNameString (moduleName md)
    mkName s = lookupOrigNameCache ch m n
      where 
        s' = reverse s
        (n', m') = Prelude.span (\c -> c /= '.') s'
        n = mkOccName OccName.varName (reverse n')
        m = if null m' then 
              md 
            else 
              md {moduleName = mkModuleName $ reverse (drop 1 m')}



{-|
  Given a trivially unsat constraint @a@, @showTypeError a@ is the 
  message that we will print out to the user as an SDoc.
-}
showTypeError :: Atomic -> SDoc
showTypeError a =
    blankLine 
      $+$ (coloured (colBold Prelude.<> colWhiteFg) $ hang topLine 2 (hang msgLine1 2 msgLine2))
      $+$ blankLine
  where
    topLine = 
      (ppr $ spanInfo a) GhcPlugins.<> colon 
      <+> coloured (sWarning defaultScheme) (text "warning:")
      <+> lbrack GhcPlugins.<> coloured (sWarning defaultScheme) (text "Intensional") GhcPlugins.<> rbrack
    msgLine1 = 
      text "Could not verify that" <+> quotes (ppr $ left a) 
        <+> text "from" 
        <+> (ppr $ getLocation (left a)) 
    msgLine2 = text "cannot reach the incomplete match at"
        <+> (ppr $ getLocation (right a))

{-|
    Given a GHC interface tycon representation @iftc@,
    @tcIFaceTyCon iftc@ is the action that returns the original tycon.
-}
tcIfaceTyCon :: IfaceTyCon -> IfL TyCon
tcIfaceTyCon iftc = do
  e <- tcIfaceExpr (IfaceType (IfaceTyConApp iftc IA_Nil))
  case e of
    Type (TyConApp tc _) -> return tc
    _ -> pprPanic "TyCon has been corrupted!" (ppr e)

data Benchmark = 
  Benchmark { 
      times :: [Integer],
      avg :: Integer,
      bigN :: Int,
      bigK :: Int,
      bigD :: Int,
      bigV :: Int,
      bigI :: Int
    }
  deriving (Generic)

instance ToJSON Benchmark
instance FromJSON Benchmark

{-|
    Given the name of a benchmark @n@ and a beginning @t0@ and end 
    time @t1@ and statistics @ss@ on the run, @recordBenchmarks n (t0, t1) ss@
    is the IO action that writes the benchmark data to a JSON file.
-}
recordBenchmarks :: String -> (Integer, Integer) -> Stats -> IO ()
recordBenchmarks name (t0, t1) stats = do
  exist <- doesFileExist "benchmark.json"
  if exist
    then
      decodeFileStrict "benchmark.json" >>= \case
        Nothing ->
          encodeFile "benchmark.json" (Map.singleton name new)
        Just bs ->
          case Map.lookup name bs of
            Nothing ->
              encodeFile "benchmark.json" (Map.insert name new bs)
            Just bench -> do
              let bench' = updateAverage $ bench {times = (t1 - t0) : times bench}
              encodeFile "benchmark.json" (Map.insert name bench' bs)
    else encodeFile "benchmark.json" (Map.singleton name new)
  where
    updateAverage b =
      b {avg = sum (times b) `div` toInteger (length (times b))}
    new =
      Benchmark
        { 
          bigN = getN stats,
          bigD = getD stats,
          bigV = getV stats,
          bigK = getK stats,
          bigI = getI stats,
          times = [t1 - t0],
          avg = t1 - t0
        }    