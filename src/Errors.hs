{-# LANGUAGE MultiParamTypeClasses #-}

module Errors
    (
      Error (ConstraintError, ApplicationError, PolyTypeError, ConstructorError, DataTypeError, InExpr)
    ) where

import Types
import GenericConGraph
import qualified GhcPlugins as Core

data Error = InExpr (Core.Expr Core.Var) Error | ConstraintError | ApplicationError | PolyTypeError | ConstructorError | DataTypeError

instance ConstraintError RVar UType Error where
  usingEquivalence = error "usingEquivalence"
  fromCycle = error "fromCycle"
  fromClosure sx sy e = e
  hetrogeneousConstructors c d = error $ show d ++ show c
  subtypeOfZero = error "subtypeOfZero"
  supertypeOfOne = error "supertypeOfOne"

instance Show Error where
  show ConstraintError = "ConstraintError"
  show ApplicationError = "ApplicationError"
  show PolyTypeError = "PolyTypeError"
  show ConstructorError = "ConstructorError"
  show DataTypeError = "DataTypeError"
  show (InExpr s e) = Core.pprPanic ("error: " ++ ", in the expr") $ Core.ppr s
