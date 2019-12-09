{-# LANGUAGE FlexibleInstances #-}
module PrettyPrint (
  format
)
where

import Prelude hiding ((<>))

import Data.List

import qualified GhcPlugins as Core
import Outputable

import Constraint hiding (empty)

-- instance Outputable Sort where
--   ppr (SVar v)       = ppr v
--   ppr (SData d)      = ppr d
--   ppr (SArrow s1 s2) = parens (ppr s1 <> arrow  <> ppr s2)
--   ppr (SApp s1 s2)   = ppr s1 <> char '@' <> ppr s2
--   ppr (SLit l)       = ppr l
--   ppr (SBase b)      = ppr b

-- instance Outputable Type where
--   ppr (Base b)          = ppr b
--   ppr (Con d k)         = ppr k
--   ppr (Sum d ks)        = char 'Σ' <> brackets (pprWithBars id (ppr <$> ks))
--   ppr Dot               = empty
--   ppr (TVar v)          = ppr v
--   ppr (t1 :=> t2)       = parens (ppr t1 <> space <> arrow <> space <> ppr t2)
--   ppr (App t1 s2)       = ppr t1 <> char '@' <> ppr s2
--   ppr (Lit l)           = ppr l

-- instance Outputable TypeScheme where
--   ppr (Forall as cg t) = hang header 3 (hang (keyword $ text "where") 3 body)
--     where
--       xs = domain cg
--       -- cs = cons cg
--       header = (if null as then empty else forAllLit <> space <> interppSP as <> dot <> space) <> (if null xs then empty else forAllLit <> space <> interppSP xs <> dot <> space) <> ppr t
--       body   = vcat [] -- (ppr <$> cs)

-- instance Outputable Guard where
--   ppr (Guard g) = ppr g

format :: Core.Name -> TypeScheme -> SDoc
format v ts = ppr v <> space <> dcolon <> space <> ppr ts