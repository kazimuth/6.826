{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Abstraction where

import qualified Prelude
import qualified Proc

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

data LayerAbstraction state1 state2 =
   Build_LayerAbstraction

type Abstraction state = LayerAbstraction Proc.Coq_world state

abstraction_compose :: (Abstraction a1) -> (LayerAbstraction a1 a2) ->
                       LayerAbstraction Proc.Coq_world a2
abstraction_compose _ _ =
  Build_LayerAbstraction

data InitResult =
   Initialized
 | InitFailed

then_init :: (Proc InitResult) -> (Proc InitResult) -> Proc InitResult
then_init init1 init2 =
  (>>=) (unsafeCoerce init1) (\r ->
    case unsafeCoerce r of {
     Initialized -> init2;
     InitFailed -> return (unsafeCoerce r)})

