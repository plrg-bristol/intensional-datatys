module Test where

data Tm = Var Int | Cst Int | App Tm Tm

subst :: (Int -> Tm) -> Tm -> Tm
subst g x = case x of
  Var i -> g i
  Cst j -> Cst j
  App y z -> App (subst g y) (subst g z)
