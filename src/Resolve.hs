module Resolve where

import Context
import Data.Map

resolve :: [(String, ConGraph)] -> Map String [(Type, Type)] -> Map String [(Type, Type)] ->
resolve
