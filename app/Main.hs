{-# LANGUAGE TypeOperators #-}

module Main where

import Expr
import Types
import Context
import ConGraph
import Inference
import Text.Parsec
import Data.Map.Strict as Map hiding (foldr, map, filter)
import Data.Functor.Const
import Control.Monad.Except
import Control.Monad.RWS
import System.IO

-- main :: IO ()
-- main = do
--     estring <- getLine
--     case parse pExpr "" estring of
--       Left err -> error $ show err
--       Right e -> putStrLn $ show e

main :: IO ()
main = putStrLn "Hello, World!"
-- main = case runExcept $ runRWST (listen $ infer expr) env 5 of
--   Left e -> mapM_ print $ getConst $ traverse Const e
--   Right r-> putStrLn "Success"
--
-- env :: Context
-- env = Context {cst = Map.empty, con = Map.fromList kvp, var = Map.empty}
--     where
--         kvp = [("Var", ("Tm", [TBase "Int"])), ("Cst", ("Tm", [TBase "Int"])), ("App", ("Tm", [TData "Tm", TData "Tm"]))]
--
-- expr = (EAbs "f" ((TBase "Int" :=> RVar "1" "Tm") :=> RVar "2" "Tm" :=> RVar "3" "Tm")
--         (EAbs "g" (TBase "Int" :=> RVar "4" "Tm")
--           (EAbs "x" (RVar "5" "Tm")
--             (ECase (EVar "x" [])
--               [
--                 ("Vor", ["i"], EApp (EVar "g" []) (EVar "i" [])),
--                 ("Cst", ["j"], EApp (ECon "Cst") (EVar "j" [])),
--                 ("App", ["y", "z"], EApp (EApp (ECon "App") (EApp (EApp (EVar "f" []) (EVar "g" [])) (EVar "y" []))) (EApp (EApp (EVar "f" []) (EVar "g" [])) (EVar "y" [])))
--               ]))))
