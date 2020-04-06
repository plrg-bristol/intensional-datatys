module SimpleTest where

import Prelude hiding (odd, even, head)

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
head (a:as) = a

test :: Int
test = head (singleton 5)
