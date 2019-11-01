module Test where

import Prelude hiding (Bool, True, False, not, List, foldr)

data Tm = Var Int | Cst Int | App Tm Tm

data Bool = True | False

-- data List a = Empty | Cons a (List a)

data List = Empty | Cons Nat List

data Nat = Z | S Nat

myAddr = (:) :: Int -> [Int] -> [Int]

subst :: (Int -> Tm) -> Tm -> Tm
subst g x = case x of
  Var i -> g i
  Cst j -> Cst j
  App y z -> App (subst g y) (subst g y)

not :: Bool -> Bool
not True = False
not False = True

isEven :: Nat -> Bool
isEven Z = True
isEven (S n) = isOdd n

isOdd :: Nat -> Bool
isOdd Z = False
isOdd (S n) = isOdd n

foldn :: (a -> a) -> a -> Nat -> a
foldn s z Z = z
foldn s z (S n) = s (foldn s z n)

add = foldn S Z
mul = add

-- Polymorphism is dodgy!
-- myerror :: Bool
-- myerror = error "Boo"
--
-- foldr :: (a -> b -> b) -> b -> (List a) -> b
-- foldr f x Empty = x
-- foldr f x (Cons a as) = f a (foldr f x as)

rebuild :: List -> a
rebuild (Cons a b) = rebuild b
