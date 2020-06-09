{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Constraints
  ( Atomic,
    Guard,
    Constraint,
    ConstraintSet (..),
    empty,
    insert,
    union,
    guardWith,
    saturate,
  )
where

import Constructors
import Control.Monad.Except hiding (guard)
import qualified Data.HashSet as HS
import Data.Hashable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import DataTypes
import GhcPlugins hiding (L, empty)
import Types

type Atomic = Constraint 'L 'R

type Guard = IM.IntMap (UniqSet Name)

data Constraint l r
  = Constraint
      { left :: K l,
        right :: K r,
        guard :: Guard,
        srcSpan :: SrcSpan
      }
  deriving (Eq)

instance Hashable (Constraint l r) where
  hashWithSalt s c = hashWithSalt s (left c, right c, IM.toList c, Constraints.srcSpan c)

-- TODO: remove empty guards
resolve :: Atomic -> Atomic -> Maybe Atomic
resolve = undefined

newtype ConstraintSet = ConstraintSet (HS.HashSet Atomic)

empty :: ConstraintSet
empty = ConstraintSet HS.empty

insert :: Atomic -> ConstraintSet -> ConstraintSet
insert a (ConstraintSet s) = ConstraintSet (HS.insert a s)

union :: ConstraintSet -> ConstraintSet -> ConstraintSet
union (ConstraintSet s) (ConstraintSet s') = ConstraintSet (HS.union s s')

guardWith :: Guard -> ConstraintSet -> ConstraintSet
guardWith g (ConstraintSet s) = ConstraintSet (HS.map (\a -> a {guard = _ (guard a) g}) s)

-- TODO: fully restrict
saturate, saturateF :: Domain -> ConstraintSet -> Except Atomic ConstraintSet
saturate xs cs = do
  cs' <- saturateF xs cs
  if cs == cs'
    then return cs
    else saturate xs cs'

saturateF xs (ConstraintSet cs) =
  ConstraintSet . HS.filter interface
    <$> foldM
      ( \cs' a ->
          foldM
            ( \cs'' a' ->
                if intermediate (right a)
                  then case resolve a a' of
                    Nothing -> return cs''
                    Just a''
                      | safe (left a'') (right a'') -> return (HS.insert a'' cs'')
                      | otherwise -> throwError a''
                  else return cs''
            )
            cs'
            cs
      )
      cs
      cs
  where
    intermediate (Dom x _) = IS.notMember x xs
    intermediate _ = False
    interface a =
      case left a of
        Dom x _ | IS.notMember x xs -> False
        _ ->
          case right a of
            Dom x _ | IS.notMember x xs -> False
            _ -> IM.foldrWithKey (\x ks p -> p && (IS.member x xs || isEmptyUniqSet ks)) True (guard a)
