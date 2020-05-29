module Formula where

type P = String

data Fm = 
    Atom P 
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
nnf fm = fm

