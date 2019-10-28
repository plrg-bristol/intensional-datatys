{-# LANGUAGE MultiParamTypeClasses #-}

module Errors
    (
      Error (VariableError, PolyTypeError, ConstructorError, DataTypeError, InExpr)
    ) where

import Prelude hiding ((<>), text)
import Types as T
import GenericConGraph
import GhcPlugins

data Error =
    InExpr (Expr Var) Error
  | VariableError Var
  | PolyTypeError Var
  | ConstructorError DataCon
  | DataTypeError TyCon DataCon
  | Hetro T.Type T.Type
  | FromClosure T.Type T.Type Error
  | UsingEq RVar T.Type Error
  | SubZero T.Type
  | FromCycle [RVar] T.Type Error
  | SuperOne T.Type

instance ConstraintError RVar UType Error where
  usingEquivalence = UsingEq
  fromCycle = FromCycle
  fromClosure = FromClosure
  hetrogeneousConstructors = Hetro
  subTypeOfZero = SubZero
  superTypeOfOne = SuperOne

instance Outputable Error where
  ppr (VariableError x) = text "The variable " <> ppr x <>text " is not in scope."
  ppr (PolyTypeError x) = text "The polymorphic variable " <> ppr x <> text " hasn't been fully instantiated."
  ppr (ConstructorError x) = text "The constructor " <> ppr x <> text " is not in scope."
  ppr (DataTypeError d k) = text "The data T.Type " <> ppr d <> text " does not have a constructor " <> ppr k <> text "."
  ppr (InExpr s e) = ppr e -- text "The error: " <> ppr e <> text " has occured in the expression: \n" <> ppr s
  ppr (Hetro c d) = text "hetrogeneousConstructors: " <> ppr c <> ppr d
  ppr (FromClosure c d e) = text "from closure: " <> ppr c <> ppr d <> text "in the error:" <> ppr e
  ppr (FromCycle xs t e) = text "from cycle " <> ppr xs <> ppr t <> text "in the error: " <> ppr e
  ppr (UsingEq xs t e) =  text "using the substitution " <> ppr xs <> ppr t <> text "in the error: " <> ppr e
