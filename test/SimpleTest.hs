module SimpleTest where

import Prelude hiding (odd, even, head, tail)

data Nat = Zero | Succ Nat

odd :: Nat -> Bool
odd Zero = False
odd (Succ n) = even n

even :: Nat -> Bool
even Zero = True
even (Succ n) = odd n

singleton :: Int -> [Int]
singleton x = [x]

head :: [a] -> a
head (a:_) = a

tail :: [a] -> [a]
tail (_:xs) = xs

hhead :: [a] -> a
hhead (_:a:_) = a

test1 :: Int
test1 = head (singleton 5)

test2 :: Int
test2 = hhead (singleton 5)

test3 :: Int
test3 = head (tail (singleton 5))
