{-# LANGUAGE CPP #-}

module Ubiq where

import qualified GhcPlugins as GHC

  -- Ubiquitous functions, they're found everywhere

debugging :: Bool
debugging = 
#ifdef DEBUG
  True
#else
  False
#endif

traceSpan :: GHC.SrcSpan -> String
traceSpan s = GHC.showSDocUnsafe (GHC.ppr s)