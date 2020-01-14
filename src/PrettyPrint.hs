{-# LANGUAGE GADTs #-}

module PrettyPrint (
)
where

import Prelude hiding ((<>))

import Outputable
import BasicTypes

import Types
import Constraint

-- Clone of a Outputable (Core.Type)
instance Outputable (Type e) where
  ppr = pprTy topPrec
    where
      pprTy :: PprPrec -> Type e -> SDoc
      pprTy _ (Var a)        = ppr a
      pprTy prec (App t1 t2) = hang (pprTy prec t1)
                                  2 (pprTy appPrec t2)
      pprTy _ (Base b)       = ppr b
      pprTy _ (Data d)       = ppr d
      pprTy prec (Inj x d)   = maybeParen prec funPrec $
                              sep [text "inj", ppr x, ppr d]
      pprTy prec (t1 :=> t2) = maybeParen prec funPrec $
                              sep [pprTy funPrec t1, arrow <+> pprTy prec t2]
      pprTy _ (Lit l)        = ppr l
      pprTy prec ty@Forall{} 
        | (tvs, body) <- split ty
        = maybeParen prec funPrec $
          hang (text "forall" <+> fsep (map ppr tvs) <> dot)
            2 (ppr body)
        where
          split ty | Forall tv ty' <- ty
                    , (tvs, body) <- split ty'
                    = (tv:tvs, body)
                    | otherwise
                    = ([], ty)

instance Outputable Guard where


instance Outputable K where
  ppr (Dom x d) = sep [text "inj", ppr x, ppr d]
  ppr (Set ks)  = pprWithBars ppr ks

instance Outputable ConSet where
  ppr cs = vcat (map ppr (toList cs))

instance Outputable TypeScheme where
  ppr (TypeScheme (xs, cs, t)) = hang (text "forall" <+> fsep (map ppr xs) <> dot <> ppr t)
                                    2 (ppr cs)