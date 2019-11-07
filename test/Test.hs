module Test where

-- import Prelude hiding (Bool, True, False, not)
-- import Utils.Containers.Internal.PtrEquality

-- import qualified GHC.Exts as GHCExts

-- data Tm = Var Int | Cst Int | App Tm Tm


-- data Bool = True | False

-- data List a = Empty | Cons a (List a)

-- data List' = Empty' | Cons' Nat List'

-- data Nat = Z | S Nat

-- myAddr :: Int -> [Int] -> [Int]
-- myAddr = (:)

-- -- -- Polymorphism is dodgy!
-- myerror :: Bool
-- myerror = error "Boo"

-- mySeven = (3 + 4, 0)

-- subst :: (Int -> Tm) -> Tm -> Tm
-- subst g x = case x of
--   Var i -> g i
--   Cst j -> Cst j
--   App y z -> App (subst g y) (subst g y)

-- not :: Bool -> Bool
-- not True = False
-- not False = True

-- filterLength3 :: Foldable t => [t a] -> [t a]
-- filterLength3 = foldr (\x rs -> if (length x) == 3 then  x : rs else rs) [] 

-- isEven :: Nat -> Bool
-- isEven Z = True
-- isEven (S n) = isOdd n

-- isOdd :: Nat -> Bool
-- isOdd Z = False
-- isOdd (S n) = isEven n

-- foldn :: (a -> a) -> a -> Nat -> a
-- foldn s z Z = z
-- foldn s z (S n) = s (foldn s z n)

-- add = foldn S Z
-- mul = add

-- foldr' :: (a -> b -> b) -> b -> (List a) -> b
-- foldr' f x Empty = x
-- foldr' f x (Cons a as) = f a (foldr' f x as)

-- rebuild :: List' -> a
-- rebuild (Cons' a b) = rebuild b

-- test1 x xs = [a | a <- xs, a <= x]

-- quicksort1 :: [Int] -> [Int]
-- quicksort1 [] = []
-- quicksort1 (x:xs) =
--   let comp1 = [a | a <- xs, a <= x]
--       comp2 = [a | a <- xs, a > x]
--   in
--   case comp1 of
--     c1'@(c1:cs1) -> 
--       case comp2 of
--         c2'@(c2:cs2) -> 
--           let smallerSorted = quicksort1 c1'
--               biggerSorted = quicksort1 c2'
--           in  smallerSorted ++ [x] ++ biggerSorted

-- test = head' []

-- head' (x:xs) = x

liftA2 :: (Applicative f, Functor f) => (a -> b -> c) -> f a -> f b -> f c
liftA2 f x = (<*>) (fmap f x)