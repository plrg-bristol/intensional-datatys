{-# LANGUAGE MultiParamTypeClasses #-}

module Errors
    (
      Error (VariableError, PolyTypeError, ConstructorError, DataTypeError, InExpr)
    ) where

import Types
import GenericConGraph
import qualified GhcPlugins as Core

data Error =
    InExpr (Core.Expr Core.Var) Error
  | VariableError Core.Var
  | PolyTypeError Core.Var
  | ConstructorError Core.Name
  | DataTypeError Core.TyCon Core.Name
  | Hetro Type Type
  | FromClosure Type Type Error

instance ConstraintError RVar UType Error where
  usingEquivalence = error "usingEquivalence"
  fromCycle = error "fromCycle"
  fromClosure = FromClosure
  hetrogeneousConstructors = Hetro
  subtypeOfZero = error "subtypeOfZero"
  supertypeOfOne = error "supertypeOfOne"

instance Show Error where
  show (VariableError x) = "The variable " ++ show x ++ " is not in scope."
  show (PolyTypeError x) = "The polymorphic variable " ++ show x ++ " hasn't been fully instantiated."
  show (ConstructorError x) = "The constructor " ++ show x ++ " is not in scope."
  show (DataTypeError d k) = "The data type " ++ show d ++ " does not have a constructor " ++ show k ++ "."
  show (InExpr s e) = Core.pprPanic ("The error: " ++ show e ++ " has occured in the expression: \n") $ Core.ppr s
  show (Hetro c d) = "hetrogeneousConstructors: " ++ show c ++ show d
  show (FromClosure c d e) = "from closure: " ++ show c ++ show d ++ "in the error:" ++ show e
