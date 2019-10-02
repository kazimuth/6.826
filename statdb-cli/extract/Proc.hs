{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Proc where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

type IO__Coq_baseOpT x = Any

type IO__Coq_world = Any

type Coq_baseOpT x = IO__Coq_baseOpT x

type Coq_world = IO__Coq_world

