module Lib
    ( plugin
    ) where

import Types
import InferM
import ConGraph
import PrettyPrint
import InferCoreExpr

import Control.Monad.RWS hiding (Sum, Alt)
import qualified Data.Map as M hiding (partition, filter, drop, foldr)
import Data.List

import Outputable
import DynFlags
import Pretty

import GhcPlugins

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoStrictness, CoreDoPluginPass "Constraint Inference" (liftIO. inferGuts)] ++ todo)

inferGuts :: ModGuts -> IO ModGuts
inferGuts guts@ModGuts{mg_binds = p, mg_tcs = tcs, mg_module = m} = do
  let env = Context{con = listToUFM (foldr buildContext [] tcs), var = M.empty}
  -- pprTraceM "" (ppr p)
  let ((ts, _), _, _) = runRWS (listen $ inferProg p) env 0
  putStrLn ""
  putStrLn $ showSDocUnsafe $ format ts
  putStrLn ""
  return guts

-- Add type constructor to underlying delta (polarisation is implicit)
buildContext :: TyCon -> [(DataCon, (TyCon, [Var], [Sort]))] -> [(DataCon, (TyCon, [Var], [Sort]))]
buildContext t xs = xs' ++ xs
  where
    xs' = foldr go [] (tyConDataCons t)

    go :: DataCon -> [(DataCon, (TyCon, [Var], [Sort]))] -> [(DataCon, (TyCon, [Var], [Sort]))]
    go d ys = (d, (t, as, sorts)):ys
      where
        sorts = toSort <$> dataConOrigArgTys d
        as = dataConUnivTyVars d --Assume no existential vars