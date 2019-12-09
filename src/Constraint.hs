{-# LANGUAGE FlexibleInstances, PatternSynonyms, BangPatterns #-}

module Constraint (
  Sort(SBase, SVar, SArrow, SData, SApp, SLit),
  Type(Base, TVar, (:=>), Inj, Sum, Con, Dot, App, Lit),
  SortScheme,
  TypeScheme,
  pattern SForall,
  pattern Forall,
  sort,
  stems,

  ConGraph,
  empty,
  domain,
  declare,
  guardWith,
  union,
  emit,
  subRefVars,

  transitive,
  restrict
) where

import Data.Bifunctor
import Data.Maybe
import qualified Data.Map as M
import qualified Data.Set as S
import Debug.Trace
import qualified Data.List as L
import qualified TyCoRep as Tcr
import qualified GhcPlugins as Core hiding ((<>))
import Prelude hiding (lookup)
import qualified Outputable as O

data Sort = 
    SBase Core.Name
  | SVar Core.Name 
  | SArrow Sort Sort 
  | SData Core.Name
  | SApp Sort Sort
  | SLit Tcr.TyLit
  deriving Eq

data Type = 
    Base Core.Name
  | TVar Core.Name
  | Type :=> Type 
  | Inj Int Core.Name
  | Sum Core.Name [Core.Name]
  | Dot
  | App Sort Sort
  | Lit Tcr.TyLit
  deriving Eq

instance O.Outputable Sort where
  ppr (SVar v)       = O.ppr v
  ppr (SData d)      = O.ppr d
  ppr (SArrow s1 s2) = O.parens (O.ppr s1 O.<> O.arrow  O.<> O.ppr s2)
  ppr (SApp s1 s2)   = O.ppr s1 O.<> O.char '@' O.<> O.ppr s2
  ppr (SLit l)       = O.ppr l
  ppr (SBase b)      = O.ppr b

instance O.Outputable Type where
  ppr (Base b)          = O.ppr b
  ppr (Con d k)         = O.ppr k
  ppr (Sum d ks)        = O.char 'Σ' O.<> O.brackets (O.pprWithBars id (O.ppr <$> ks))
  ppr Dot               = O.empty
  ppr (TVar v)          = O.ppr v
  ppr (Inj x d)         = O.ppr x O.<> O.ppr d
  ppr (t1 :=> t2)       = O.parens (O.ppr t1 O.<> O.space O.<> O.arrow O.<> O.space O.<> O.ppr t2)
  ppr (App t1 s2)       = O.ppr t1 O.<> O.char '@' O.<> O.ppr s2
  ppr (Lit l)           = O.ppr l
  

pattern Con :: Core.Name -> Core.Name -> Type
pattern Con d k = Sum d [k]

-- The underlying sort
sort :: Type -> Sort
sort (Base b)     = SBase b
sort (TVar a)     = SVar a
sort (t1 :=> t2)  = SArrow (sort t1) (sort t2)
sort (Inj _ d)    = SBase d
sort (Sum d _)    = SBase d
sort (App s1 s2)  = SApp s1 s2
sort (Lit l)      = SLit l

trivial :: Type -> Type -> Bool
trivial (Base b) (Inj _ d) | b == d = True
trivial (Inj _ d) (Base b) | b == d = True
trivial t1 t2 = t1 == t2

-- Subrefinement variables which appear in the type
injs :: Type -> [(Int, Core.Name)]
injs (t1 :=> t2) = injs t1 ++ injs t2
injs (Inj i d)   = [(i, d)]
injs _           = []

stems :: Type -> [Int]
stems (t1 :=> t2) = stems t1 ++ stems t2
stems (Inj i d)   = [i]
stems _           = []

-- An unrefined sort scheme
type SortScheme = ([Core.Name], Sort)

pattern SForall :: [Core.Name] -> Sort -> SortScheme
pattern SForall as u = (as, u)

-- Refinement quantified sort scheme
newtype TypeScheme = TS ([Core.Name], ConGraph, Type)

instance O.Outputable TypeScheme where
  ppr (Forall as cg t) = O.hang header 3 (O.hang (O.keyword $ O.text "where") 3 body)
    where
      xs = domain cg
      cs = M.toList $ cons cg
      header = (if null as then O.empty else O.forAllLit O.<> O.space O.<> O.interppSP as O.<> O.dot O.<> O.space) O.<> (if null xs then O.empty else O.forAllLit O.<> O.space O.<> O.interppSP xs O.<> O.dot O.<> O.space) O.<> O.ppr t
      body   = (O.ppr cs)

pattern Forall :: [Core.Name] -> ConGraph -> Type -> TypeScheme
pattern Forall as cg t = TS (as, cg, t)





-- Internal representation of atomic constraints
data Constraint = 
    SubEnv Int Int                      -- X <= Y
  | ConDom Core.Name Int Core.Name      -- k in dom(X(d))
  | DomConSet Int Core.Name [Core.Name] -- dom(X(d)) <= K
  deriving (Eq, Ord)

instance O.Outputable Constraint where
  ppr (SubEnv x y) = O.ppr x O.<> O.char '<' O.<> O.ppr y
  ppr (ConDom k x d) = O.ppr k O.<> O.char '<' O.<> O.ppr x O.<> O.ppr d
  ppr (DomConSet x d ks) = O.ppr x O.<> O.ppr d O.<> O.char '<' O.<> O.ppr ks

-- A guard is either (Just) a list of construcotr inclusion constraints
-- or trivially false, i.e. Nothing. Trivially true guards are encoded as Just []
type Guard = Maybe [(Core.Name, Int, Core.Name)]

maybeSubGuard :: Constraint -> Guard -> Maybe Guard
maybeSubGuard (SubEnv x y) (Just g)
  | any (\(_, x', _) -> y == x') g = Just $ Just $ L.nub $ subEnvVarGuard x y g
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
  | g `subsume` g' = mergeGuards g gs
  | otherwise      = g' : mergeGuards g gs
  where
    -- Partial order: g' entails g
    subsume :: Guard -> Guard -> Bool
    subsume (Just g) (Just g') = all (`elem` g') g
    subsume _ _ = False

cross :: [Guard] -> [Guard] -> [Guard]
cross gs gs' = foldr mergeGuards [] [g <> g' | g <- gs, g' <- gs']





      
type ConSet = M.Map Constraint [Guard]

data ConGraph = ConGraph {
  -- Disjunctive list guards
  cons    :: ConSet,

-- The height of a variable is a datatype, such that the variable is
-- a subrefinement environemnt of the datatypes's slice
  heights :: M.Map Int [Core.Name]
} deriving Eq

instance O.Outputable ConGraph where
  ppr cg = O.ppr (Forall [] cg Dot)

domain :: ConGraph -> [Int]
domain = M.keys . heights

empty :: ConGraph
empty = ConGraph { cons = M.empty, heights = M.empty }

union :: ConGraph -> ConGraph -> ConGraph
union ConGraph { cons = c, heights = h } ConGraph { cons = c', heights = h' } = ConGraph { cons = c `M.union` c', heights = M.unionWith L.union h h'}

-- Declare a new subrefinement environment variable
-- Skips stems that already occurs
declare :: Int -> Core.Name -> ConGraph -> ConGraph
declare x d cg = cg{heights = M.insertWith L.union x [d] $ heights cg}

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
  | sort t1 /= sort t2 = Core.pprPanic "Sorts must align!" (Core.ppr (t1, t2, e))
simplify t1 t2 _
  | trivial t1 t2 = []
simplify (t11 :=> t12) (t21 :=> t22) e = simplify t21 t11 e ++ simplify t12 t22 e
simplify (Inj x d) (Sum _ ks) _  = [DomConSet x d ks]
simplify (Con d k) (Inj x _) _   = [ConDom k x d]
simplify (Con d k) (Sum d' (k':ks)) e
  | k == k'   = []
  | otherwise = simplify (Con d k) (Sum d' ks) e
simplify (Sum d ks) t e        = concatMap (\k -> simplify (Con d k) t e) ks
simplify (Inj x _) (Inj y _) _ = [SubEnv x y]
simplify Con{} (Sum _ []) e    = error "Unsatisfiable!" -- Throw e related error
simplify t1 t2 _               = Core.pprPanic "Invalid subtyping constraint!" (Core.ppr (t1, t2))

-- Emit a new subtyping constraint
-- Declare any new stems
emit :: Type -> Type -> Guard -> ConGraph -> Core.Expr Core.Var -> ConGraph
-- emit t1 t2 _ _ e | Core.pprTrace "emit" (Core.ppr (t1, t2)) False = undefined
emit t1 t2 g cg e = foldr (uncurry declare) cg' (injs t1 ++ injs t2)
  where
    -- Insert new constraint and merge any existing guard
    cs  = simplify t1 t2 e
    cg' = cg{cons = foldr (mergeInsert g) (cons cg) cs}

-- Add a guard to all constraints
guardWith :: Core.Name -> Type -> ConGraph -> ConGraph
guardWith k (Inj x d') cg = cg{cons = fmap (mergeGuards (Just [(k, x, d')])) (cons cg)}
guardWith k (Sum _ ks) cg
  | k `elem` ks = cg
  | otherwise   = error "Constructor is not in the sum!"
guardWith _ _ _ = error "Type doesn't contain constructors!"





class SubRefVars t where
  subRefVar :: Int -> Int -> t -> t

subRefVars :: SubRefVars t => [Int] -> [Int] -> t -> t
subRefVars [] _ t = t
subRefVars _ [] t = t
subRefVars (x:xs) (y:ys) t = subRefVar x y $ subRefVars xs ys t

instance SubRefVars ConGraph where
  subRefVar x y ConGraph{cons = c, heights = h} = ConGraph{cons = subRefVar x y c, heights = M.mapKeys f h}
    where
      f :: Int -> Int
      f z
        | z == x    = y
        | otherwise = z
    
instance SubRefVars ConSet where
  subRefVar x y = M.fromList . fmap (bimap (subRefVar x y) (subRefVar x y)) . M.toList 

instance SubRefVars Constraint where
  subRefVar x y (SubEnv z1 z2) = SubEnv z1' z2'
    where
      z1' = if x == z1 then y else z1
      z2' = if x == z2 then y else z2
  subRefVar x y (ConDom k z d) = ConDom k z' d
    where
      z' = if z == x then y else z
  subRefVar x y (DomConSet z d k) = DomConSet z' d k
    where
      z' = if z == x then y else z

instance SubRefVars [Guard] where
  subRefVar x y = fmap (fmap (fmap go))
    where
      go :: (Core.Name, Int, Core.Name) -> (Core.Name, Int, Core.Name)
      go (k, z, d) = (k, if x == z then y else z, d)
    
instance SubRefVars Type where
  subRefVar x y (Inj z d)
    | x == z    = Inj y d
    | otherwise = Inj z d
  subRefVar _ _ t = t





-- Perform the transitive closure of a set of constraints
transitive :: ConGraph -> ConGraph
transitive cg
  | cg' == cg = cg
  | otherwise            = cg'
  where
    cg' = resGuard' $ transitive' cg

-- transitive' cg | Core.pprTrace "transitive'" (Core.ppr ()) False = undefined
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

restrict :: [Int] -> ConGraph -> ConGraph
restrict xs ConGraph{cons = c, heights = h} = ConGraph{cons = M.mapMaybeWithKey f c, heights = M.restrictKeys h (S.fromList xs)}
  where
    f :: Constraint -> [Guard] -> Maybe [Guard]
    f (SubEnv x y) gs
      | x `elem` xs && y `elem` xs = Just $ filter f' gs
      | otherwise                  = Nothing
    f (ConDom k x d) gs
      | x `elem` xs = Just $ filter f' gs
      | otherwise   = Nothing
    f (DomConSet x d ks) gs
      | x `elem` xs = Just $ filter f' gs
      | otherwise = Nothing
    
    f' :: Guard -> Bool
    f' Nothing = True
    f' (Just gs) = all (\(k, x, d) -> x `elem` xs) gs