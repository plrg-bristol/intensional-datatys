{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE PatternSynonyms #-}

module Intensional.Scheme
  ( Scheme,
    SchemeGen (..),
    pattern Forall,
    mono,
    Intensional.Scheme.unsats
  )
where

import Binary
import Intensional.Constraints as Constraints
import qualified Data.IntSet as I
import qualified Data.IntMap as IntMap
import GhcPlugins 
import Intensional.Types

type Scheme = SchemeGen TyCon

-- Constrained polymorphic types
data SchemeGen d
  = Scheme
      { tyvars :: [Name],
        boundvs :: Domain,
        body :: TypeGen d,
        constraints :: ConstraintSet
      }
  deriving (Functor, Foldable, Traversable)

{-# COMPLETE Forall #-}

pattern Forall :: [Name] -> TypeGen d -> SchemeGen d
pattern Forall as t <-
  Scheme as _ t _
  where
    Forall as t = Scheme as mempty t mempty

instance Outputable d => Outputable (SchemeGen d) where
  ppr = prpr ppr

instance Binary d => Binary (SchemeGen d) where
  put_ bh (Scheme as bs t cs) = put_ bh as >> put_ bh (I.toList bs) >> put_ bh t >> put_ bh cs

  get bh = Scheme <$> get bh <*> (I.fromList <$> get bh) <*> get bh <*> get bh

instance Outputable d => Refined (SchemeGen d) where
  domain s = (domain (body s) Prelude.<> domain (constraints s)) I.\\ boundvs s

  rename x y s
    | I.member x (boundvs s) = s
    | I.member y (boundvs s) = pprPanic "Alpha renaming of polymorphic types is not implemented!" $ ppr (x, y)
    | otherwise =
      Scheme
        { tyvars = tyvars s,
          boundvs = boundvs s,
          body = rename x y (body s),
          constraints = rename x y (constraints s)
        }
  
  prpr _ scheme 
    | constraints scheme /= mempty =
      hang
        (hcat [pprTyQuant, pprConQuant, prpr varMap (body scheme)])
        2
        (hang (text "where") 2 (prpr varMap (constraints scheme)))
    | otherwise = hcat [pprTyQuant, pprConQuant, prpr varMap (body scheme)]
    where
      numVars = I.size (domain scheme)
      varNames =
        if numVars > 3 then [ char 'X' GhcPlugins.<> int n | n <- [1..numVars] ] else [ char c | c <- ['X', 'Y', 'Z'] ]
      varMap = \x -> m IntMap.! x
        where m = IntMap.fromList $ zip (I.toAscList (boundvs scheme)) varNames
      pprTyQuant
        | null (tyvars scheme) = empty
        | otherwise = hcat [forAllLit <+> fsep (map ppr $ tyvars scheme), dot]
      pprConQuant
        | I.null (boundvs scheme) = empty
        | otherwise = hcat [forAllLit <+> fsep (map varMap $ I.toList (boundvs scheme)), dot]

-- Demand a monomorphic type
mono :: SchemeGen d -> TypeGen d
mono (Forall [] t) = t
mono _ = Ambiguous

{-|
    Given a scheme @s@, @unsats s@ is the constraint set containing
    just the trivially unsatisfiable constraints associated with @s@.
-}
unsats :: Scheme -> ConstraintSet
unsats s = Constraints.unsats (constraints s)
