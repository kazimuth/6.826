{-# OPTIONS_GHC -F -pgmF ./fiximports.py #-}
{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module StatDbCli where

import qualified Prelude
import qualified Abstraction
import qualified StatDbAPI
import qualified VariablesAPI
import qualified VariablesImpl

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

_Coq_statdb__add :: Prelude.Integer -> Proc ()
_Coq_statdb__add v =
  (>>=) (unsafeCoerce VariablesImpl._Vars__read VariablesAPI.VarSum) (\sum ->
    (>>=) (unsafeCoerce VariablesImpl._Vars__read VariablesAPI.VarCount)
    (\count -> (>>=)
    (unsafeCoerce VariablesImpl._Vars__write VariablesAPI.VarSum
      ((Prelude.+) (unsafeCoerce sum) v)) (\_ -> (>>=)
    (unsafeCoerce VariablesImpl._Vars__write VariablesAPI.VarCount
      ((Prelude.+) (unsafeCoerce count) (Prelude.succ 0))) (\_ -> return
    ()))))

_Coq_statdb__mean :: Proc (Prelude.Maybe Prelude.Integer)
_Coq_statdb__mean =
  (>>=) (unsafeCoerce VariablesImpl._Vars__read VariablesAPI.VarSum) (\sum ->
    (>>=) (unsafeCoerce VariablesImpl._Vars__read VariablesAPI.VarCount)
    (\count ->
    (\fO fS n -> if n Prelude.== 0 then fO () else fS (n Prelude.- 1))
      (\_ -> return Prelude.Nothing)
      (\n -> return (Prelude.Just
      ((\n m -> if m Prelude.== 0 then 0 else Prelude.div n m)
        (unsafeCoerce sum) (Prelude.succ n))))
      (unsafeCoerce count)))

_Coq_statdb__init' :: Proc Abstraction.InitResult
_Coq_statdb__init' =
  (>>=) (unsafeCoerce VariablesImpl._Vars__write VariablesAPI.VarCount 0)
    (\_ -> (>>=)
    (unsafeCoerce VariablesImpl._Vars__write VariablesAPI.VarSum 0) (\_ ->
    return Abstraction.Initialized))

_Coq_statdb__init :: Proc Abstraction.InitResult
_Coq_statdb__init =
  Abstraction.then_init VariablesImpl._Vars__init _Coq_statdb__init'

_Coq_statdb__recover :: Proc ()
_Coq_statdb__recover =
  VariablesImpl._Vars__recover

_Coq_statdb__abstr :: Abstraction.Abstraction StatDbAPI.State
_Coq_statdb__abstr =
  Abstraction.abstraction_compose VariablesImpl._Vars__abstr
    Abstraction.Build_LayerAbstraction

get_new_item :: Proc Prelude.Integer
get_new_item = CLI.Stubs.getNewItem

report_mean :: (Prelude.Maybe Prelude.Integer) -> Proc ()
report_mean = CLI.Stubs.reportMean

loop :: Proc ()
loop =
  (>>=) (unsafeCoerce _Coq_statdb__mean) (\m -> (>>=)
    (unsafeCoerce report_mean m) (\_ -> (>>=) (unsafeCoerce get_new_item)
    (\x -> (>>=) (unsafeCoerce _Coq_statdb__add x) (\_ -> loop))))

cli :: Proc ()
cli =
  (>>=) (unsafeCoerce _Coq_statdb__init) (\init_ok ->
    case unsafeCoerce init_ok of {
     Abstraction.Initialized -> loop;
     Abstraction.InitFailed -> return ()})

