module Utils (
  slice,
  refinable
) where

import qualified Data.List as L

import qualified GhcPlugins as Core
import qualified TyCoRep as Tcr

-- Take the slice of a datatype
slice :: Core.TyCon -> [Core.TyCon]
slice d = sliceClose [d]

sliceClose s
  | s' == s   = s
  | otherwise = sliceClose s'
  where
    s' = L.nub $ [s'' | t <- s, d <- Core.tyConDataCons t, (Tcr.TyConApp tc _) <- Core.dataConOrigArgTys d, refinable tc, s'' <- slice tc]

-- Decides whether a datatypes only occurs positively
refinable :: Core.TyCon -> Bool
refinable tc = (length (Core.tyConDataCons tc) > 1) && all pos (concatMap Core.dataConOrigArgTys $ Core.tyConDataCons tc)
    where
      pos :: Core.Type -> Bool
      pos (Tcr.FunTy t1 t2) = neg t1 && pos t2
      pos _                 = True

      neg :: Core.Type -> Bool
      neg (Tcr.TyConApp tc' _)               | tc == tc' = False
      neg (Tcr.AppTy (Tcr.TyConApp tc' _) _) | tc == tc' = False 
      neg (Tcr.TyVarTy _)   = False -- Type variables may be substituted with the type itself
                                    -- Perhaps it is possible to record whether a type variable occurs +/-
      neg (Tcr.FunTy t1 t2) = pos t1 && neg t2
      neg _                 = True
