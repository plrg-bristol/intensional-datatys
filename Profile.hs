module Main where

import Lib
import GHC as G
import GhcMake as G
import DynFlags
import SrcLoc as G
import Plugins

import Control.Monad
import Control.Monad.IO.Class
import System.Environment

import Lib

-- cabal new-profile -- +RTS -pj -l-au

initGhcM :: [String] -> Ghc ()
initGhcM xs = do
    df1 <- getSessionDynFlags
    let df1' = df1{staticPlugins = [StaticPlugin (PluginWithArgs plugin [])]}
    let cmdOpts = ["-fforce-recomp"] ++ xs
    (df2, leftovers, warns) <- G.parseDynamicFlags df1' (map G.noLoc cmdOpts)
    setSessionDynFlags df2
    ts <- mapM (flip G.guessTarget Nothing) $ map unLoc leftovers

    setTargets ts

    void $ G.load LoadAllTargets

main :: IO ()
main = do
    xs <- words <$> readFile "args"
    let libdir = "/opt/ghc/8.8.3/lib/ghc-8.8.3"
    runGhc (Just libdir) $ initGhcM xs
