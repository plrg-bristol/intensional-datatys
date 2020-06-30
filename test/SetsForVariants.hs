module SetsForVariants where

-- Examples from the introduction to
-- Set Theoretic Types for Polymorphic Variants
-- by Castagna, Petrucciani and Nguyen

data T = A | B | C

id2 x = 
  case x of
      A -> x
      B -> x

xs = [id2 A, C]

ys = [A, B]

f x = 
    case id2 x of
      A -> B
      y -> y

g x = 
    case x of 
        A -> id2 x
        _ -> x

h (A,_) = 1
h (_,B) = 2
h (_,A) = 3
h (B,_) = 4
