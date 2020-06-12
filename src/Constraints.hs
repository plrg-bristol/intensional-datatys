{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}

module Constraints
  ( Atomic,
    Guard,
    Constraint (..),
    ConstraintSet (..),
    empty,
    insert,
    union,
    guardWith,
    saturate,
  )
where

import Binary
import Constructors
import Control.Monad.Except hiding (guard)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import DataTypes
import GhcPlugins hiding (L, empty)
import Types
import Unique
import Prelude hiding ((<>))

type Atomic = Constraint 'L 'R

type Guard = IM.IntMap (HM.HashMap Level (UniqSet Name))

instance {-# OVERLAPPING #-} Outputable Guard where
  ppr g =
    hcat
      [ ppr k <> ppr l <> elem <> text "dom" <> parens (ppr x)
        | (x, kls) <- IM.toList g,
          (l, ks) <- HM.toList kls,
          k <- nonDetEltsUniqSet ks
      ]
    where
      elem = unicodeSyntax (char '∈') (text " in ")

instance {-# OVERLAPPING #-} Binary Guard where
  get bh = fmap (fmap mkUniqSet . HM.fromList) . IM.fromList <$> get bh

  put_ bh = put_ bh . fmap (fmap (fmap (fmap nonDetEltsUniqSet))) . IM.toList . fmap HM.toList

instance Refined Guard where
  domain = IM.keysSet

  rename x y = IM.mapKeys (\z -> if z == x then y else z)

data Constraint l r
  = Constraint
      { left :: K l,
        right :: K r,
        guard :: Guard,
        srcSpan :: SrcSpan
      }
  deriving (Eq)

instance Outputable (Constraint l r) where
  ppr a = ppr (guard a) <+> char '?' <+> ppr (left a) <+> arrowt <+> ppr (right a)

instance (Binary (K l), Binary (K r)) => Binary (Constraint l r) where
  put_ bh c = put_ bh (left c) >> put_ bh (right c) >> put_ bh (guard c) >> put_ bh (Constraints.srcSpan c)
  get bh = Constraint <$> get bh <*> get bh <*> get bh <*> get bh

instance Refined (Constraint l r) where
  domain c = domain (left c) `IS.union` domain (right c) `IS.union` domain (guard c)

  rename x y c =
    c
      { left = rename x y (left c),
        right = rename x y (right c),
        guard = rename x y (guard c)
      }

instance Hashable (Constraint l r) where
  hashWithSalt s c = hashWithSalt s (left c, right c, IM.toList . fmap (fmap (fmap (getKey . getUnique) . nonDetEltsUniqSet)) $ guard c)

-- Checks if the guard implies the body
tautology :: Atomic -> Bool
tautology a
  | Dom x d <- right a,
    Con k _ <- left a,
    Just True <- elementOfUniqSet k <$> (IM.lookup x (guard a) >>= HM.lookup (level d)) =
    True
tautology a = False

trans :: Atomic -> Atomic -> [Atomic]
trans l r
  | Dom x d <- right l, -- Trans
    Dom y d' <- left r,
    x == y,
    d == d' =
    [ r
        { left = left l,
          guard = IM.unionWith (HM.unionWith unionUniqSets) (guard l) (guard r)
        }
    ]
  | otherwise = []

weak :: Atomic -> Atomic -> [Atomic]
weak l r
  | Dom x d <- right l, -- Weakening
    Con k _ <- left l =
    [ r
        { guard = IM.adjust (HM.adjust (`delOneFromUniqSet` k) (level d)) x $ IM.unionWith (HM.unionWith unionUniqSets) (guard l) (guard r)
        }
    ]
  | otherwise = []

subs :: Atomic -> Atomic -> [Atomic]
subs l r
  | Dom x d <- right l, -- Substitution
    Dom y d' <- left l,
    Just ks <- nonDetEltsUniqSet <$> (IM.lookup y (guard l) >>= HM.lookup (level d')) =
    [ r'
      | k <- ks,
        let r' =
              r
                { guard =
                    IM.insertWith (HM.unionWith unionUniqSets) x (HM.singleton (level d) (unitUniqSet k))
                      $ IM.adjust (HM.adjust (`delOneFromUniqSet` k) (level d')) y
                      $ IM.unionWith
                        (HM.unionWith unionUniqSets)
                        (guard l)
                        (guard r)
                },
        not (tautology r')
    ]
  | otherwise = []

-- TODO: make direct lookups
newtype ConstraintSet = ConstraintSet (HS.HashSet Atomic)
  deriving (Eq)

instance Outputable ConstraintSet where
  ppr (ConstraintSet s) = vcat (ppr <$> HS.toList s)

instance Binary ConstraintSet where
  put_ bh (ConstraintSet s) = put_ bh $ HS.toList s
  get bh = ConstraintSet . HS.fromList <$> get bh

instance Refined ConstraintSet where
  domain (ConstraintSet s) = foldr (IS.union . domain) IS.empty s

  rename x y (ConstraintSet s) = ConstraintSet $ HS.map (rename x y) s

empty :: ConstraintSet
empty = ConstraintSet HS.empty

insert :: Atomic -> ConstraintSet -> ConstraintSet
insert a (ConstraintSet s) = ConstraintSet (HS.insert a s)

union :: ConstraintSet -> ConstraintSet -> ConstraintSet
union (ConstraintSet s) (ConstraintSet s') = ConstraintSet (HS.union s s')

guardWith :: Guard -> ConstraintSet -> ConstraintSet
guardWith g (ConstraintSet s) = ConstraintSet (HS.map (\a -> a {guard = IM.unionWith (HM.unionWith unionUniqSets) (guard a) g}) s)

-- TODO: lookup based on right hand side
saturate :: Domain -> ConstraintSet -> Except Atomic ConstraintSet
saturate xs cs = saturate' (domain cs `IS.difference` xs) cs
  where
    saturate' is cs | IS.null is = return cs
    saturate' is cs = do
      ConstraintSet cs' <- saturateF (IS.findMin is) cs
      if cs == ConstraintSet cs'
        then saturate (IS.deleteMin is) (ConstraintSet $ HS.filter intermediate cs')
        else saturate is (ConstraintSet cs')
      where
      intermediate a =
        case left a of
          Dom x _ | x == IS.findMin is -> False
          _ ->
            case right a of
              Dom x _ | x == IS.findMin is -> False
              _ ->
                IM.foldrWithKey
                  ( \x xgs p ->
                      all
                        ( \ks ->
                            x /= IS.findMin is|| isEmptyUniqSet ks
                        )
                        xgs
                        && p
                  )
                  True
                  (guard a)

saturateF :: RVar -> ConstraintSet -> Except Atomic ConstraintSet
saturateF x (ConstraintSet cs) =
  foldM
    ( \cs' a ->
        case right a of
          Dom y _ | x == y -> 
            foldM
              ( \cs'' a' ->
                  foldM
                    ( \cs''' a'' ->
                        if safe (left a'') (right a'')
                          then return (insert a'' cs''')
                          else throwError a''
                    )
                    cs''
                    (trans a a' ++ subs a a' ++ weak a a')
              )
              cs'
              cs
          _ -> return cs'
    )
    (ConstraintSet cs)
    cs