module SimpleTest where

import Prelude hiding (odd, even)

data Nat = Zero | Succ Nat

odd :: Nat -> Bool
odd Zero = False
odd (Succ n) = even n

even :: Nat -> Bool
even Zero = True
even (Succ n) = odd n