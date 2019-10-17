module Lib
    ( plugin
    ) where

import Data.List hiding (insert)
import Data.Word
import TyCon
import Inference
import qualified Expr as E
import TcRnTypes
import Data.Map as Map hiding (filter, drop)
import Context
import Types
import GhcPlugins
import Control.Monad.RWS hiding (Sum, Alt)
import Control.Monad.Except
import Debug.Trace

env :: Context
env = Context {cst = Map.empty, con = Map.fromList kvp, var = Map.empty}
    where
        kvp = [("$main$Test$Var", ("$main$Test$Tm", [SBase "$ghc-prim$GHC.Types$Int"])), ("$main$Test$Cst", ("$main$Test$Tm", [SBase "$ghc-prim$GHC.Types$Int"])), ("$main$Test$App", ("$main$Test$Tm", [SData "$main$Test$Tm", SData "$main$Test$Tm"]))]

plugin :: Plugin
plugin = defaultPlugin { installCoreToDos = install }
  where
    install _ todo = return ([ CoreDoPluginPass "Constraint Inference" (liftIO. inferGuts)] ++ todo)

inferGuts :: ModGuts -> IO ModGuts
inferGuts guts = do
    -- let env' = getEnv $ mg_binds guts
    let binds = filter fil $ mg_binds guts
    let ms = fmap makeBinds binds
    case runExcept $ runRWST (listen $ mapM inferModule ms) env 0 of
      Left err -> putStrLn "Inference error: " >> print err >> return guts
      Right ((m, _), _, _) -> putStrLn "Success" >> print m >> return guts
  where
    makeBinds (NonRec v expr) = [(E.name v, E.getTypeScheme expr, E.fromCoreExpr expr)]
    makeBinds (Rec bs) = E.getBinds bs

    fil (NonRec v expr) = let s = E.name v in isPrefixOf "$main$Test$" s && not (isPrefixOf "$main$Test$$" s)
    fil (Rec bs) = True

-- getEnv :: [Bind CoreBndr] -> Context
-- getEnv [] = Context {cst = Map.empty, con = Map.empty, var = Map.empty}
-- getEnv (NonRec v expr:bs)
--   | isPrefixOf "$main$Test$$tc'" n = Context {cst = Map.empty, con = con', var = Map.empty}
--   | otherwise = env
--   where
--     n = E.name v
--     con' = con $ getEnv bs
--     -- con'' = insert ("$main$Test$" ++ drop 14 n) (d, args) con'
-- getEnv (Rec r:bs) = error "Unimplemented"

-- disp'' :: Annotation -> String
-- disp'' ann = case fromSerialized (deserializeWithData :: [Word8] -> String) $ ann_value ann of
--     Nothing -> ""
--     Just s -> s ++ " @ " ++ case ann_target ann of
--               NamedTarget n -> show $ nameStableString n
--
-- disp' :: TyCon -> String
-- disp' t = "Name: " ++ (show $ nameStableString $ tyConName t) ++
--           ", Arity: " ++ (show $ tyConArity t) ++
--           ", Cons: " ++ concatMap (nameStableString . getName) (tyConDataCons t)
--
-- disp :: CoreBind -> String
-- disp (NonRec v expr) = show v ++ " = " ++ dispExpr expr
-- disp (Rec bs) = concatMap (show . fst) bs
--
-- dispExpr :: Expr Var -> String
-- dispExpr (Var i) = show i
-- dispExpr (Lit l) = show l
-- dispExpr (App expr arg) = "(" ++ dispExpr expr ++ ") (" ++ dispExpr arg ++ ")"
-- dispExpr (Lam v expr) = "(\\" ++ show v ++ "." ++ dispExpr expr ++ ")"
-- dispExpr (Let b expr) = "(let (" ++ disp b ++ ") in (" ++ dispExpr expr ++ ")"
-- dispExpr _ = ""
--
-- conMapFil :: (a -> String) -> (String -> Bool) -> [a] -> String
-- conMapFil s f [] = ""
-- conMapFil s f (a:as) =
--   if f (s a)
--   then (s a) ++ "\n" ++ conMapFil s f as
--   else conMapFil s f as
