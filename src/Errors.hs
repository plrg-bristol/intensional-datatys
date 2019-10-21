{-# LANGUAGE MultiParamTypeClasses #-}

module Errors
    (
      Error (ConstraintError, ApplicationError, PolyTypeError, ConstructorError, DataTypeError)
    ) where

import Types
import GenericConGraph

data Error = ConstraintError | ApplicationError | PolyTypeError | ConstructorError | DataTypeError

instance ConstraintError RVar UType Error where
  usingEquivalence = undefined
  fromCycle = undefined
  fromClosure = undefined
  hetrogeneousConstructors = undefined
  subtypeOfZero = undefined
  supertypeOfOne = undefined

instance Show Error where
  show = undefined
