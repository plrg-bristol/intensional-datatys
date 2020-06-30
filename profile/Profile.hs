module Main where

import Control.Monad
import GHC
import Lib
import Plugins
import System.Environment

-- cabal new-run profile -- +RTS -pj -l-au
-- https://www.speedscope.app/

main :: IO ()
main = do
  files <- getArgs
  runGhc (Just "/opt/ghc/8.8.3/lib/ghc-8.8.3") $ do
    df1 <- getSessionDynFlags
    let cmdOpts = ["-fforce-recomp", "-O0", "-prof", "-fprof-auto", "-g"] ++ files
    (df2, leftovers, warns) <-
      parseDynamicFlags
        (df1 {staticPlugins = [StaticPlugin (PluginWithArgs plugin [])]})
        (map noLoc cmdOpts)
    setSessionDynFlags df2
    ts <- mapM (flip guessTarget Nothing . unLoc) leftovers
    setTargets ts
    void $ load LoadAllTargets
