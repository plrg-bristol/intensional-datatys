module SimpleTest where

import Prelude (Int)

data Nat = Zero | Succ Nat

data Bool = True | False

data List a = Nil | Cons a (List a)

odd :: Nat -> Bool
odd Zero = False
odd (Succ n) = even n

even :: Nat -> Bool
even Zero = True
even (Succ n) = odd n

singleton :: a -> List a
singleton a = Cons a Nil

head :: List a -> a
head (Cons a _) = a

tail :: List a -> List a
tail (Cons _ as) = as

second :: List a -> a
second (Cons a (Cons b _)) = b

skipTwo :: List a -> List a
skipTwo (Cons a (Cons b as)) = as

data T = A | B

-- type error only detected by 
-- model building 
modelTest :: T -> Int
modelTest x = case (modelTest B, x) of (_, A) -> 0
