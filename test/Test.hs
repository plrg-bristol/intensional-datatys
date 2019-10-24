module Test where

import Prelude hiding (Bool, True, False, not)

data Tm = Var Int | Cst Int | App Tm Tm

data Bool = True | False

data Nat = Z | S Nat

subst :: (Int -> Tm) -> Tm -> Tm
subst g x = case x of
  Var i -> g i
  Cst j -> Cst j
  App y z -> App (subst g y) (subst g z)

not :: Bool -> Bool
not True = False
not False = True

isOdd :: Nat -> Bool
isOdd Z = False
isOdd (S n) = not (isEven (S n))

isEven :: Nat -> Bool
isEven Z = True
isEven (S n) = not (isOdd (S n))
