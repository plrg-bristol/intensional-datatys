module Main where

import Control.Monad
import Control.Monad.IO.Class
import DynFlags
import EnumSet
import GHC
import Intensional
import Plugins
import System.Directory
import System.Environment
import System.FilePath.Posix
import System.IO
import System.Timeout
import CmdLineParser

data Mode
  = Profile
  | BenchmarkInit
  | Benchmark
  deriving (Eq)

compileWithPlugin :: Mode -> IO ()
compileWithPlugin m = do
  args <- words <$> readFile "profile/self-args"
  runGhc (Just "/opt/ghc/8.8.3/lib/ghc-8.8.3") $ do
    df1 <- getSessionDynFlags
    (df2, leftover, ws) <-
      parseDynamicFlags
        df1
          { -- ghcLink = NoLink,
            -- optLevel = 0,
            -- enableTimeStats = m == Profile,
            -- generalFlags = fromList (Opt_ForceRecomp : [Opt_SccProfilingOn | m == Profile]),
            -- profAuto = if m == Profile then NoProfAuto else ProfAutoAll,
            staticPlugins =
              [ StaticPlugin
                  ( PluginWithArgs
                      plugin
                      ( "suppress-output"
                          : case m of
                            Profile -> []
                            Benchmark -> ["benchmark"]
                            BenchmarkInit -> ["benchmark'"]
                      )
                  )
              ]
          }
        (map noLoc args)
    liftIO $ mapM_ (print . warnReason) ws
    setSessionDynFlags df2
    mapM ((`guessTarget` Nothing) . unLoc) leftover >>= setTargets
    void $ load LoadAllTargets

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["-p", file] -> do
      -- requires +RTS -pj -l-au
      compileWithPlugin Profile
      renameFile "profile.prof" ("profile/" ++ takeBaseName file ++ ".prof")
      removeFile "profile.eventlog"
    ["-b"] -> benchmark
      -- listDirectory "test/XMonad" >>= benchmark . fmap ("test/XMonad/" ++)
    -- ("-b" : files) -> benchmark -- Run benchmarks on particular files
    _ -> putStrLn "Invalid command line argument!"
  where
    benchmark :: IO ()
    benchmark = do
      -- appendFile "benchmarks" ("Running: " ++ file ++ "\n")
      b <- timeout 10000000 (compileWithPlugin BenchmarkInit)
      case b of
        Nothing -> return ()
        Just _ -> loop 9
    loop 0 = return ()
    loop n = do
      b <- timeout 10000000 (compileWithPlugin Benchmark)
      case b of
        Nothing -> return ()
        Just _ -> loop (n - 1)