{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
module VariablesImpl where

import qualified Prelude
import qualified Abstraction
import qualified VariablesAPI

_Vars__init :: Proc Abstraction.InitResult
_Vars__init = Variables.Ops.init

_Vars__read :: VariablesAPI.Coq_var -> Proc Prelude.Integer
_Vars__read = Variables.Ops.read

_Vars__write :: VariablesAPI.Coq_var -> Prelude.Integer -> Proc ()
_Vars__write = Variables.Ops.write

_Vars__recover :: Proc ()
_Vars__recover =
  Prelude.error "AXIOM TO BE REALIZED"

_Vars__abstr :: Abstraction.Abstraction VariablesAPI.State
_Vars__abstr =
  Prelude.error "AXIOM TO BE REALIZED"

