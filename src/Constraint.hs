module Constraint (
  ConGraph,
  emptyCG,
  unionCG,
  emit,
  guardWith,
  fromList,

  TypeScheme(..)
) where

import Data.Maybe
import Data.Map hiding (foldr, mapMaybe, fromList)
import qualified Data.List as L
import qualified GhcPlugins as Core hiding ((<>))
import Debug.Trace
import Prelude hiding (lookup)
import Type



data TypeScheme = Forall [Core.Name] [Int] [(Guard, Type, Type)] Type


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






      
type ConSet = Map Constraint [Guard]

data ConGraph = ConGraph {
  -- Disjunctive list guards
  cons    :: ConSet,

-- The height of a variable is a datatype, such that the variable is
-- a subrefinement environemnt of the datatypes's slice
  heights :: Map Int Core.Name
} deriving Eq

emptyCG :: ConGraph
emptyCG = ConGraph { cons = empty, heights = empty }

fromList :: [(Guard, Type, Type)] -> Core.Expr Core.Var -> ConGraph
fromList cs e = foldr (\(g, t1, t2) cg' -> emit t1 t2 g cg' e) emptyCG cs 

unionCG :: ConGraph -> ConGraph -> ConGraph
unionCG ConGraph { cons = c, heights = h } ConGraph { cons = c', heights = h' } = ConGraph { cons = c `union` c', heights = h `union` h'}

-- Declare a new subrefinement environment variable
-- Skips stems that already occu
declare :: Int -> Core.Name -> ConGraph -> ConGraph
declare x d cg = cg{heights = insertWith (flip const) x d $ heights cg}

-- Insert a new internal constraint 
mergeInsert :: Guard -> Constraint -> ConSet -> ConSet
mergeInsert g c m = 
  case lookup c m of
    Nothing -> insert c [g] m
    Just g' -> insert c (mergeGuards g g') m

-- Insert a constraint with a disjunction of guards
mergeInsertMany :: ConSet -> [Guard] -> Constraint -> ConSet
mergeInsertMany m gs c = foldr (`mergeInsert` c) m gs

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
cross gs gs' = foldr mergeGuards [] $ [g <> g' | g <- gs, g' <- gs']





-- Emit a new subtyping constraint
-- Declare any new stems
emit :: Type -> Type -> Guard -> ConGraph -> Core.Expr Core.Var -> ConGraph
emit t1 t2 g cg e = foldr (uncurry declare) cg' (injs t1 ++ injs t2)
  where
    -- Insert new constraint and merge any existing guard
    cs  = simplify t1 t2 e
    cg' = cg{cons = foldr (mergeInsert g) (cons cg) cs}

-- Reduce subtyping relation to atomic constraint
simplify :: Type -> Type -> Core.Expr Core.Var -> [Constraint]
simplify Dot _ _ = []
simplify _ Dot _ = []
simplify t1 t2 _
  | t1 == t2 = []
simplify (t11 :=> t12) (t21 :=> t22) e = simplify t21 t11 e ++ simplify t12 t22 e
simplify (Inj x d as) (Sum ks as') e
  | as == as'                          = [DomConSet x d ks]
simplify (Con k as) (Inj x d as') e 
  | as == as'                          = [ConDom k x d]
simplify (Con k as) (Sum (k':ks) as') e
  | k == k' && as == as'        = []
  | as == as'                   = simplify (Con k as) (Sum ks as') e
simplify (Sum ks as) t e        = concatMap (\k -> simplify (Con k as) t e) ks
simplify (Con k _) (Sum [] _) e = undefined

-- Add a guard to all constraints
guardWith :: Core.Name -> Type -> ConGraph -> ConGraph
guardWith d t cg = undefined




-- Perform the transitive closure of a set of constraints
transitive :: ConGraph -> ConGraph
transitive cg
  | transitive' cg == cg = cg
  | otherwise            = transitive $ transitive' cg

transitive' cg = cg{cons = foldlWithKey go (cons cg) (cons cg)}
  where
    go :: Map Constraint [Guard] -> Constraint -> [Guard] -> ConSet
    go cons c g = foldlWithKey (go' c g) cons cons

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
resGuard' cg = cg{cons = foldlWithKey go (cons cg) (cons cg)}
  where
    go :: Map Constraint [Guard] -> Constraint -> [Guard] -> ConSet
    go cons c g = foldlWithKey (go' c g) cons cons

    -- Potentially substitute a guard into a constraints
    go' :: Constraint -> [Guard] -> ConSet -> Constraint -> [Guard] -> ConSet
    go' c g cons' c' g' = mergeInsertMany cons' g'' c'
      where
        g'' = mapMaybe (maybeSubGuard c) g'
