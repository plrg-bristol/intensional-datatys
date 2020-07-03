module Main where

import Control.Monad
import Criterion.Main
import Criterion.Main.Options
import GHC
import Lib
import Plugins
import System.Directory
import System.Environment
import System.FilePath.Posix

compileWithPlugin :: Bool -> [FilePath] -> IO ()
compileWithPlugin prof files =
  runGhc (Just "/opt/ghc/8.8.3/lib/ghc-8.8.3") $ do
    df1 <- getSessionDynFlags
    let cmdOpts =
          if prof
            then ["-fforce-recomp", "-O0", "-prof", "-fprof-auto", "-g"]
            else ["-fforce-recomp", "-O0"]
    (df2, _, _) <-
      parseDynamicFlags
        (df1 {staticPlugins = [StaticPlugin (PluginWithArgs plugin ["suppress-output"])]})
        (map noLoc cmdOpts)
    setSessionDynFlags df2
    ts <- mapM (`guessTarget` Nothing) files
    setTargets ts
    void $ load LoadAllTargets

defaults = ["test/SimpleTest.hs", "test/DNF.hs"]

main :: IO ()
main = do
  args <- getArgs
  case args of
    ("-p" : files) -> do
      -- requires +RTS -pj -l-au
      when (length files > 1) $
        putStrLn "Warning: multiple files cannot be profiled separately."
      compileWithPlugin True files
      renameFile "profile.prof" ("profile/" ++ takeBaseName (head files) ++ ".prof")
      removeFile "profile.eventlog"
    ["-b"] -> benchmark defaults -- Run default benchmarks
    ("-b" : files) -> benchmark files -- Run benchmarks on particular files
    _ -> putStrLn "Invalid command line argument!"
  where
    benchmark :: [FilePath] -> IO ()
    benchmark files =
      runMode
        ( Run
            defaultConfig
            Glob
            ( fmap takeBaseName files
            )
        )
        [ bench
            (takeBaseName f)
            ( nfIO
                (compileWithPlugin False [f])
            )
          | f <- files
        ]
