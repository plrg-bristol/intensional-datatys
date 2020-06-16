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
import Control.Monad.Except hiding ((<>), guard)
import Control.Monad.Writer hiding ((<>), guard)
import Data.Bifunctor
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Monoid hiding ((<>))
import DataTypes
import GhcPlugins hiding (L, empty, filterOut)
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

instance Eq (Constraint l r) where
  Constraint l r g _ == Constraint l' r' g' _ = l == l' && r == r' && g == g'

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
tautology _ = False

trans :: Atomic -> Atomic -> [Atomic]
trans l r
  | Dom x d <- right l, -- Trans
    Dom y d' <- left r,
    x == y,
    d == d' =
    [ r'
      | let r' =
              r
                { left = left l,
                  guard = IM.unionWith (HM.unionWith unionUniqSets) (guard l) (guard r)
                },
        not (tautology r')
    ]
  | otherwise = []

weak :: Atomic -> Atomic -> [Atomic]
weak l r
  | Dom x d <- right l, -- Weakening
    Con k _ <- left l =
    [ r'
      | let r' =
              r
                { guard = IM.adjust (HM.adjust (`delOneFromUniqSet` k) (level d)) x $ IM.unionWith (HM.unionWith unionUniqSets) (guard l) (guard r)
                },
        not (tautology r')
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

recursive :: Atomic -> Bool
recursive a =
  case right a of
    Dom x d -> maybe False isEmptyUniqSet (IM.lookup x (guard a) >>= HM.lookup (level d))
    _ -> False

data ConstraintSet
  = ConstraintSet
      { definite :: IM.IntMap (HS.HashSet Atomic),
        goal :: HS.HashSet Atomic
      }
  deriving (Eq)

member :: Atomic -> ConstraintSet -> Bool
member a cs =
  case right a of
    Dom x _ ->
      case IM.lookup x (definite cs) of
        Nothing -> False
        Just as -> HS.member a as
    _ -> HS.member a (goal cs)

instance Outputable ConstraintSet where
  ppr cs = vcat ((ppr . HS.toList . snd <$> IM.toList (definite cs)) ++ (ppr <$> HS.toList (goal cs)))

instance Binary ConstraintSet where
  put_ bh cs = put_ bh (second HS.toList <$> IM.toList (definite cs)) >> put_ bh (HS.toList (goal cs))
  get bh = ConstraintSet . IM.fromList . fmap (second HS.fromList) <$> get bh <*> (HS.fromList <$> get bh)

instance (Eq a, Hashable a, Refined a) => Refined (HS.HashSet a) where
  domain = foldr (IS.union . domain) IS.empty
  rename x y = HS.map (rename x y)

instance Refined ConstraintSet where
  domain cs =
    foldr
      (IS.union . domain)
      (foldr (IS.union . domain) IS.empty (goal cs))
      (definite cs)

  rename x y cs =
    ConstraintSet
      { definite =
          IM.fromListWith HS.union $
            (\(z, s) -> (if z == x then y else z, HS.map (rename x y) s)) <$> IM.toList (definite cs),
        goal = HS.map (rename x y) (goal cs)
      }

empty :: ConstraintSet
empty = ConstraintSet {definite = IM.empty, goal = HS.empty}

insert :: Atomic -> ConstraintSet -> ConstraintSet
insert a cs =
  case right a of
    Dom x _ -> cs {definite = IM.insertWith HS.union x (HS.singleton a) (definite cs)}
    _ -> cs {goal = HS.insert a (goal cs)}

union :: ConstraintSet -> ConstraintSet -> ConstraintSet
union cs cs' =
  ConstraintSet
    { definite = IM.unionWith HS.union (definite cs) (definite cs'),
      goal = HS.union (goal cs) (goal cs')
    }

guardWith :: Guard -> ConstraintSet -> ConstraintSet
guardWith g cs =
  ConstraintSet
    { definite = IM.map (HS.map go) (definite cs),
      goal = HS.map go (goal cs)
    }
  where
    go a = a {guard = IM.unionWith (HM.unionWith unionUniqSets) (guard a) g}

filterOut :: RVar -> ConstraintSet -> ConstraintSet
filterOut x cs =
  ConstraintSet
    { definite =
        IM.mapMaybeWithKey
          ( \y s ->
              if x == y
                then Nothing
                else Just (HS.filter intermediate s)
          )
          (definite cs),
      goal = HS.filter intermediate (goal cs)
    }
  where
    intermediate a =
      case left a of
        Dom y _ | y == x -> False
        _ ->
          case right a of
            Dom y _ | y == x -> False
            _ ->
              IM.foldrWithKey
                ( \y ygs p ->
                    all
                      ( \ks ->
                          y /= x || isEmptyUniqSet ks
                      )
                      ygs
                      && p
                )
                True
                (guard a)

saturate :: Domain -> ConstraintSet -> Except Atomic ConstraintSet
saturate xs cs = saturate' (domain cs `IS.difference` xs) cs
  where
    saturate' is cs | IS.null is = return cs
    saturate' is cs = do
      let x = IS.findMin is
      (cs', Any new) <- runWriterT $ saturateF x cs
      if new
        then saturate' is cs'
        else saturate' (IS.deleteMin is) (filterOut x cs')

saturateF :: RVar -> ConstraintSet -> WriterT Any (Except Atomic) ConstraintSet
saturateF x cs =
  case IM.lookup x (definite cs) of
    Just rs
      | not (all recursive rs) ->
        foldM
          ( \cs' a -> do
              alpha <-
                foldM -- TODO: a direct lookup here?
                  ( foldM
                      ( \cs'' a' ->
                          foldM
                            ( \cs''' a'' ->
                                case toAtomic (left a'') (right a'') of
                                  Nothing -> throwError a''
                                  Just as ->
                                    foldM
                                      ( \cs (l, r) -> do
                                          let a = a'' {left = l, right = r}
                                          if member a cs
                                            then return cs
                                            else do
                                              tell (Any True)
                                              return (insert a cs)
                                      )
                                      cs'''
                                      as
                            )
                            cs''
                            (trans a a' ++ subs a a' ++ weak a a')
                      )
                  )
                  cs'
                  (definite cs)
              beta <-
                foldM
                  ( \cs'' a' ->
                      foldM
                        ( \cs''' a'' ->
                            case toAtomic (left a'') (right a'') of
                              Nothing -> throwError a''
                              Just as ->
                                foldM
                                  ( \cs (l, r) -> do
                                      let a = a'' {left = l, right = r}
                                      if member a cs
                                        then return cs
                                        else do
                                          tell (Any True)
                                          return (insert a cs)
                                  )
                                  cs'''
                                  as
                        )
                        cs''
                        (trans a a' ++ subs a a' ++ weak a a')
                  )
                  alpha
                  (goal cs)
              if recursive a
                then return beta
                else return beta {definite = IM.adjust (HS.delete a) x (definite beta)}
          )
          cs
          rs
    _ -> return cs
