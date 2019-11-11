module Test where

data Tm = Var Int | Cst Int | App Tm Tm

data List a = Empty | Cons a (List a)

type List' = List Nat -- = Empty' | Cons' Nat List'

data Nat = Z | S Nat

myAddr :: Int -> [Int] -> [Int]
myAddr = (:)

myerror :: Bool
myerror = error "Boo"

mySeven = (3 + 4, 0)

subst :: (Int -> Tm) -> Tm -> Tm
subst g x = case x of
  Var i -> g i
  Cst j -> Cst j
  App y z -> App (subst g y) (subst g y)

not :: Bool -> Bool
not True = False
not False = True

filterLength3 :: Foldable t => [t a] -> [t a]
filterLength3 = foldr (\x rs -> if (length x) == 3 then  x : rs else rs) [] 

isEven :: Nat -> Bool
isEven Z = True
isEven (S n) = isOdd n

isOdd :: Nat -> Bool
isOdd Z = False
isOdd (S n) = isEven n

foldn :: (a -> a) -> a -> Nat -> a
foldn s z Z = z
foldn s z (S n) = s (foldn s z n)

add = foldn S Z
mul = add

foldr' :: (a -> b -> b) -> b -> (List a) -> b
foldr' f x Empty = x
foldr' f x (Cons a as) = f a (foldr' f x as)

rebuild :: List' -> a
rebuild (Cons a b) = rebuild b

test1 x xs = [a | a <- xs, a <= x]

quicksort1 :: [Int] -> [Int]
quicksort1 [] = []
quicksort1 (x:xs) =
  let comp1 = [a | a <- xs, a <= x]
      comp2 = [a | a <- xs, a > x]
      smallerSorted = quicksort1 comp1
      biggerSorted = quicksort1 comp2
  in smallerSorted ++ [x] ++ biggerSorted

liftA2 :: (Applicative f, Functor f) => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x = (<*>) (fmap f x)

-- test = head' []

head' (x:xs) = x