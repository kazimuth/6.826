{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module Helpers where

import qualified Prelude
import qualified Bool

type EqualDec a = a -> a -> Prelude.Bool

equal_dec :: (EqualDec a1) -> a1 -> a1 -> Prelude.Bool
equal_dec equalDec =
  equalDec

nat_equal_dec :: EqualDec Prelude.Integer
nat_equal_dec =
  (Prelude.==)

bool_equal_dec :: EqualDec Prelude.Bool
bool_equal_dec =
  Bool.bool_dec

