{-# LANGUAGE PatternSynonyms #-}

module Constraint (
  Sort(SBase, SVar, SArrow, SData, SApp, SLit),
  Type(Base, TVar, (:=>), Inj, Sum, Con, Dot, App, Lit),
  TypeScheme,
  pattern Forall,
  sort,

  ConGraph,
  empty,
  guardWith,
  union,
  emit
) where

import Data.Maybe
import qualified Data.Map as M
import qualified Data.List as L
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core hiding ((<>))
import Debug.Trace
import Prelude hiding (lookup)

data Sort = 
    SBase Core.Name                 [Sort]
  | SVar Core.Name 
  | SArrow Sort Sort 
  | SData Core.Name                 [Sort] 
  | SApp Sort Sort
  | SLit Tcr.TyLit
  deriving Eq

data Type = 
    Base Core.Name                  [Sort]
  | TVar Core.Name
  | Type :=> Type 
  | Inj Int Core.Name               [Sort]
  | Sum Core.Name [Core.Name]       [Sort]
  | Dot
  | App Sort Sort
  | Lit Tcr.TyLit
  deriving Eq

pattern Con :: Core.Name -> Core.Name -> [Sort] -> Type
pattern Con d k as = Sum d [k] as

-- The underlying sort
sort :: Type -> Sort
sort (Base b as)  = SBase b as
sort (TVar a)     = SVar a
sort (t1 :=> t2)  = SArrow (sort t1) (sort t2)
sort (Inj _ d as) = SData d as
sort (Sum d _ as) = SData d as
sort (App s1 s2)  = SApp s1 s2
sort (Lit l)      = SLit l

-- Subrefinement variables which appear in the type
injs :: Type -> [(Int, Core.Name)]
injs (t1 :=> t2) = injs t1 ++ injs t2
injs (Inj i d _) = [(i, d)]
injs _           = []

-- Refinement quantified sort scheme
type TypeScheme = ([Core.Name], ConGraph, Type)

pattern Forall :: [Core.Name] -> ConGraph -> Type -> TypeScheme
pattern Forall as cg t = (as, cg, t)





-- Internal representation of atomic constraints
data Constraint = 
    SubEnv Int Int                      -- X <= Y
  | ConDom Core.Name Int Core.Name      -- k in dom(X(d))
  | DomConSet Int Core.Name [Core.Name] -- dom(X(d)) <= K
  deriving (Eq, Ord)

-- A guard is either (Just) a list of construcotr inclusion constraints
-- or trivially false, i.e. Nothing. Trivially true guards are encoded as Just []
type Guard = Maybe [(Core.Name, Int, Core.Name)]

domain :: Int -> [(Core.Name, Int, Core.Name)] -> Bool
domain x = any (\(_, x', _) -> x == x')

maybeSubGuard :: Constraint -> Guard -> Maybe Guard
maybeSubGuard (SubEnv x y) (Just g)
  | y `domain` g        = Just $ Just $ L.nub $ subEnvVarGuard x y g
maybeSubGuard (ConDom k x d) (Just g)
  | (k, x, d) `elem` g  = Just $ Just $ L.nub $ subConDom k x d g
maybeSubGuard _ _       = Nothing
    
subEnvVarGuard :: Int -> Int -> [(Core.Name, Int, Core.Name)] -> [(Core.Name, Int, Core.Name)]
subEnvVarGuard x y = fmap go
  where
    go :: (Core.Name, Int, Core.Name) -> (Core.Name, Int, Core.Name)
    go (k, y', d)
      | y == y'    = (k, x, d)
      | otherwise  = (k, y', d)

subConDom :: Core.Name -> Int -> Core.Name -> [(Core.Name, Int, Core.Name)] -> [(Core.Name, Int, Core.Name)]
subConDom k x d = mapMaybe go
  where
    go :: (Core.Name, Int, Core.Name) -> Maybe (Core.Name, Int, Core.Name)
    go (k', x', d')
      | k == k' && x == x' && d == d' = Nothing
      | otherwise                     = Just (k', x', d')

-- Potentially add a new guard or subsumed an existing guard
mergeGuards :: Guard -> [Guard] -> [Guard]
mergeGuards g [] = [g]
mergeGuards g (g':gs)
  | g `subsume` g' = g  : gs
  | otherwise      = g' : mergeGuards g gs
  where
    -- Partial order: g' entails g
    subsume :: Guard -> Guard -> Bool
    subsume g g' = all (`elem` g') g

cross :: [Guard] -> [Guard] -> [Guard]
cross gs gs' = foldr mergeGuards [] [g <> g' | g <- gs, g' <- gs']





      
type ConSet = M.Map Constraint [Guard]

data ConGraph = ConGraph {
  -- Disjunctive list guards
  cons    :: ConSet,

-- The height of a variable is a datatype, such that the variable is
-- a subrefinement environemnt of the datatypes's slice
  heights :: M.Map Int Core.Name
} deriving Eq

empty :: ConGraph
empty = ConGraph { cons = M.empty, heights = M.empty }

union :: ConGraph -> ConGraph -> ConGraph
union ConGraph { cons = c, heights = h } ConGraph { cons = c', heights = h' } = ConGraph { cons = c `M.union` c', heights = h `M.union` h'}

-- Declare a new subrefinement environment variable
-- Skips stems that already occu
declare :: Int -> Core.Name -> ConGraph -> ConGraph
declare x d cg = cg{heights = M.insertWith (flip const) x d $ heights cg}

-- Insert a new internal constraint 
mergeInsert :: Guard -> Constraint -> ConSet -> ConSet
mergeInsert g c m = 
  case M.lookup c m of
    Nothing -> M.insert c [g] m
    Just g' -> M.insert c (mergeGuards g g') m

-- Insert a constraint with a disjunction of guards
mergeInsertMany :: ConSet -> [Guard] -> Constraint -> ConSet
mergeInsertMany m gs c = foldr (`mergeInsert` c) m gs

-- Reduce subtyping relation to atomic constraint
simplify :: Type -> Type -> Core.Expr Core.Var -> [Constraint]
simplify Dot _ _ = []
simplify _ Dot _ = []
simplify t1 t2 e
  | sort t1 /= sort t2 = error "Sorts must align!"
simplify t1 t2 _
  | t1 == t2 = []
simplify (t11 :=> t12) (t21 :=> t22) e = simplify t21 t11 e ++ simplify t12 t22 e
simplify (Inj x d _) (Sum _ ks _) _    = [DomConSet x d ks]
simplify (Con d k as) (Inj x _ as') _  = [ConDom k x d]
simplify (Con d k as) (Sum d' (k':ks) as') e
  | k == k'   = []
  | otherwise = simplify (Con d k as) (Sum d' ks as') e
simplify (Sum d ks as) t e        = concatMap (\k -> simplify (Con d k as) t e) ks
simplify Con{} (Sum _ [] _) e     = error "Unsatisfiable!" -- Throw e related error
simplify _ _ _                    = error "Invalid subtyping constraint!"

-- Emit a new subtyping constraint
-- Declare any new stems
emit :: Type -> Type -> Guard -> ConGraph -> Core.Expr Core.Var -> ConGraph
emit t1 t2 g cg e = foldr (uncurry declare) cg' (injs t1 ++ injs t2)
  where
    -- Insert new constraint and merge any existing guard
    cs  = simplify t1 t2 e
    cg' = cg{cons = foldr (mergeInsert g) (cons cg) cs}

-- Add a guard to all constraints
guardWith :: Core.Name -> Type -> ConGraph -> ConGraph
guardWith k (Inj x d' as) cg = cg{cons = fmap (mergeGuards (Just [(k, x, d')])) (cons cg)}
guardWith k (Sum _ ks _) cg
  | k `elem` ks = cg
  | otherwise   = error "Constructor is not in the sum!"
guardWith _ _ _ = error "Type doesn't contain constructors!"





-- Perform the transitive closure of a set of constraints
transitive :: ConGraph -> ConGraph
transitive cg
  | transitive' cg == cg = cg
  | otherwise            = transitive $ transitive' cg

transitive' cg = cg{cons = M.foldlWithKey go (cons cg) (cons cg)}
  where
    go :: M.Map Constraint [Guard] -> Constraint -> [Guard] -> ConSet
    go cons c g = M.foldlWithKey (go' c g) cons cons

    -- Combine a pair of guarded constraints
    go' :: Constraint -> [Guard] -> ConSet -> Constraint -> [Guard] -> ConSet
    go' c g cons' c' g' = maybe cons' (mergeInsertMany cons' g'') c''
      where
        c'' = close c c'
        g'' = cross g g'

    -- Combine constraints if they share a node
    close :: Constraint -> Constraint -> Maybe Constraint
    close (SubEnv x y) (SubEnv y' z)
      | y == y' = Just (SubEnv x  z)
      | x == z  = Just (SubEnv y' y)
    close (SubEnv x y) (ConDom k x' d)
      | x == x' = Just (ConDom k y d)
    close (SubEnv x y) (DomConSet y' d ks)
      | y == y' = Just (DomConSet x d ks)
    close (ConDom k x' d) (SubEnv x y)
      | x == x' = Just (ConDom k y d)
    close (DomConSet y' d ks) (SubEnv x y)
      | y == y' = Just (DomConSet x d ks)
    close _ _ = Nothing

-- Perform the ResGuard closure of a set of constraints
resGuard :: ConGraph -> ConGraph
resGuard cg
  | resGuard' cg == cg = cg
  | otherwise          = resGuard $ resGuard' cg

resGuard' :: ConGraph -> ConGraph
resGuard' cg = cg{cons = M.foldlWithKey go (cons cg) (cons cg)}
  where
    go :: M.Map Constraint [Guard] -> Constraint -> [Guard] -> ConSet
    go cons c g = M.foldlWithKey (go' c g) cons cons

    -- Potentially substitute a guard into a constraints
    go' :: Constraint -> [Guard] -> ConSet -> Constraint -> [Guard] -> ConSet
    go' c g cons' c' g' = mergeInsertMany cons' g'' c'
      where
        g'' = mapMaybe (maybeSubGuard c) g'
