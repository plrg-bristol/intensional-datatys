module PrettyPrint (
  format
)
where

import Prelude hiding ((<>))

import Data.List

import qualified GhcPlugins as Core
import Outputable

import Types

instance Outputable Sort where
  ppr (SVar v)       = ppr v
  ppr (SData d as)   = ppr d <> fsep (punctuate (char '@') (ppr <$> as))
  ppr (SArrow s1 s2) = parens (ppr s1 <> arrow  <> ppr s2)
  ppr (SApp s1 s2)   = ppr s1 <> char '@' <> ppr s2
  ppr (SLit l)       = ppr l
  ppr (SBase b as)   = ppr b <> fsep (punctuate (char '@') (ppr <$> as))

instance Outputable RVar where
  ppr (RVar (x, d, as)) = braces (ppr x <> ppr (SData d as))

instance Outputable DataCon where
  ppr (DataCon (n, as, ts)) = ppr n

instance Outputable Type where
  ppr (Var r)           = ppr r
  ppr (Con _ _ d as ts) = ppr d <> fsep (punctuate (char '@') (ppr <$> as)) <> fsep (ppr <$> ts)
  ppr (Sum _ _ as c)    = char 'Σ' <> brackets (pprWithBars id [ppr d <> fsep (punctuate (char '@') (ppr <$> as)) <> fsep (ppr <$> ts)| (d, ts) <- c])
  ppr Dot               = empty
  ppr (TVar v)          = ppr v
  ppr (t1 :=> t2)       = parens (ppr t1 <> space <> arrow <> space <> ppr t2)
  ppr (App t1 s2)       = ppr t1 <> char '@' <> ppr s2
  ppr (Lit l)           = ppr l
  ppr (Base b as)       = ppr b <> fsep (punctuate (char '@') (ppr <$> as))

instance Outputable TypeScheme where
  ppr (Forall as xs cs t) = hang header 3 (hang (keyword $ text "where") 3 body)
    where
      header = (if null as then empty else forAllLit <> space <> interppSP as <> dot <> space) <> (if null xs then empty else forAllLit <> space <> interppSP xs <> dot <> space) <> ppr t
      body   = vcat (ppr <$> cs)

format :: Core.Name -> TypeScheme -> SDoc
format v ts = ppr v <> space <> dcolon <> space <> ppr ts