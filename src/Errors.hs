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

-- instance ConstraintError RVar UType Error where
--   insertionConflict t1 t2 cg = error ""

instance Outputable Error where
  ppr (VariableError x) = text "The variable " <> ppr x <>text " is not in scope."
  ppr (PolyTypeError x) = text "The polymorphic variable " <> ppr x <> text " hasn't been fully instantiated."
  ppr (ConstructorError x) = text "The constructor " <> ppr x <> text " is not in scope."
  ppr (DataTypeError d k) = text "The data T.Type " <> ppr d <> text " does not have a constructor " <> ppr k <> text "."
  ppr (InExpr s e) = text "The error: " <> ppr e <> text " has occured in the expression: \n" <> ppr s
