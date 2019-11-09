module Lib
    ( plugin
    ) where

import Control.Monad.RWS

import qualified Data.Map as M
-- import Data.Serialize

import Types
import InferM
import PrettyPrint
import InferCoreExpr

import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoStrictness, CoreDoPluginPass "Constraint Inference" (liftIO. inferGuts)] ++ todo)

inferGuts :: ModGuts -> IO ModGuts
inferGuts guts@ModGuts{mg_binds = p, mg_tcs = tcs, mg_module = m} = do
  let env = Context{var = M.empty}
  -- pprTraceM "" (ppr p)
  let (tss, _) = runInferM (inferProg p) env 0
  mapM_ (\(v, ts) -> do
    putStrLn ""
    putStrLn $ showSDocUnsafe $ format v ts
    putStrLn ""
    ) tss
  -- let ser = encode tss
  return guts