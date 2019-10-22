module Lib
    ( plugin
    ) where

import Data.List
import Data.Map as Map hiding (filter, drop)
import InferCoreExpr
import GhcPlugins
import InferM
import Utils
import Types
import Control.Monad.RWS hiding (Sum, Alt)
import Control.Monad.Except
import Debug.Trace
import TyCoRep

env :: Context
env = Context {con = Map.empty, var = Map.empty}
    where
        -- kvp = [("$main$Test$Var", ("$main$Test$Tm", [SBase "$ghc-prim$GHC.Types$Int"])),
        --        ("$main$Test$Cst", ("$main$Test$Tm", [SBase "$ghc-prim$GHC.Types$Int"])),
        --        ("$main$Test$App", ("$main$Test$Tm", [SData "$main$Test$Tm", SData "$main$Test$Tm"])),
        --        ("$main$Test$True", ("$main$Test$Bool", [])),
        --        ("$main$Test$False", ("$main$Test$Bool", [])),
        --        ("$main$Test$Z", ("$main$Test$Nat", [])),
        --        ("$main$Test$S", ("$main$Test$Nat", [SData "$main$Test$Nat"]))]
--
plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoPluginPass "Constraint Inference" (liftIO. inferGuts)] ++ todo)

inferGuts :: ModGuts -> IO ModGuts
inferGuts guts = do
    let p = filter (\b -> (all (isType . varType) $ bindersOf b) && (all isOfMain $ bindersOf b)) $ mg_binds guts
    case runExcept $ runRWST (listen $ inferProg p) env 0 of
      Left err -> putStrLn "Inference error: " >> print err >> return guts
      Right ((m, _), _, _) -> putStrLn "Success" >> print (show m) >> return guts
    return guts
  where
    isType (TyVarTy _) = True
    isType (FunTy _ _) = True
    isType _ = False

    isOfMain b = let s = name b in isPrefixOf "$main$Test$" s && not (isPrefixOf "$main$Test$$" s
