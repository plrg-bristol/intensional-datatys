module Main where

import qualified Data.List as List

type P = Int

data L = Atom P | NegAtom P
  deriving Eq

data Fm = 
    Lit L
    | Not Fm
    | And Fm Fm
    | Or Fm Fm
    | Imp Fm Fm

nnf :: Fm -> Fm
nnf (And p q) = And (nnf p) (nnf q)
nnf (Or p q) = Or (nnf p) (nnf q)
nnf (Imp p q) = Or (nnf (Not p)) (nnf q) 
nnf (Not (Not p)) = nnf p 
nnf (Not (And p q)) = Or (nnf (Not p)) (nnf (Not q))
nnf (Not (Or p q)) = And (nnf (Not p)) (nnf (Not q))
nnf (Not (Imp p q)) = And (nnf p) (nnf (Not q))
nnf (Not (Lit (Atom x))) = Lit (NegAtom x)
nnf (Not (Lit (NegAtom x))) = Lit (Atom x)
nnf (Lit (Atom x)) = Lit (Atom x)
nnf (Lit (NegAtom x)) = Lit (NegAtom x)

distrib xss yss = List.nub [ List.union xs ys | xs <- xss, ys <- yss ]

nnf2dnf (And p q) = distrib (nnf2dnf p) (nnf2dnf q)
nnf2dnf (Or p q) = List.union (nnf2dnf p) (nnf2dnf q)
nnf2dnf (Lit a) = [[a]]

dnf = nnf2dnf . nnf

k x y = x

data Arith = L Int | Plus | Mult
data Lam = Cst Arith | App Lam Lam | Abs (Lam -> Lam) | FVr String | BVr Int

lkup :: [(String,a)] -> String -> a
lkup ((s,x):ps) t = if s == t then x else lkup ps t

cloSub :: [(String, Lam)] -> Lam -> Lam
cloSub m (FVr s) = lkup m s
cloSub m (Cst c) = Cst c
cloSub m (App u v) = App (cloSub m u) (cloSub m v)

f :: Lam -> Lam
f x = k x (f (f x))

-- Bugs

nnf' :: Fm -> Fm
nnf' (And p q) = And (nnf' p) (nnf' q)
nnf' (Or p q) = Or (nnf' p) (nnf' q)
nnf' (Imp p q) = Or (Not (nnf' p)) (nnf' q) 
nnf' (Not (Not p)) = nnf' p 
nnf' (Not (And p q)) = Or (nnf' (Not p)) (nnf' (Not q))
nnf' (Not (Or p q)) = And (nnf' (Not p)) (nnf' (Not q))
nnf' (Not (Imp p q)) = And (nnf' p) (nnf' (Not q))
nnf' (Not (Lit (Atom x))) = Lit (NegAtom x)
nnf' (Not (Lit (NegAtom x))) = Lit (Atom x)
nnf' (Lit (Atom x)) = Lit (Atom x)
nnf' (Lit (NegAtom x)) = Lit (NegAtom x)

dnf' = nnf2dnf . nnf'

willNotCrash = dnf' (And (Lit (Atom 1)) (Lit (Atom 2)))
willCrash = dnf' (Imp (Lit (Atom 1)) (Lit (Atom 2)))

main :: IO ()
main = return ()
