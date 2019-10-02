{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module VariablesAPI where

import qualified Prelude

data Coq_var =
   VarCount
 | VarSum

data State =
   Coq_mkState Prelude.Integer Prelude.Integer

