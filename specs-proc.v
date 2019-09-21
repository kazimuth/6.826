Global Set Implicit Arguments.
Global Generalizable All Variables.
(* turn this on to enforce strict bulleting and braces (every tactic must apply
to a single goal) *)
Global Set Default Goal Selector "!".

Module IO.
Inductive Model :=
  { baseOpT : Type -> Type;
    world : Type;
    world_crash : world -> world;
    base_step: forall T, baseOpT T -> world -> T -> world -> Prop;
  }.
End IO.

Axiom baseModel : IO.Model.
Definition baseOpT : Type -> Type := IO.baseOpT baseModel.

 CoInductive proc (T : Type) : Type :=
| BaseOp (op : baseOpT T)
| Ret (v : T)
| Bind (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T).

Require Extraction.
Extraction Language Haskell.

Extract Inductive proc => "Proc"
                           ["error 'accessing BaseOp'" "return" "(>>=)"]
                           "(\fprim fret fbind -> error 'pattern match on proc')".

Definition world : Type := IO.world baseModel.

Print baseModel.

Inductive Result T :=
| Finished (v:T) (w:world)
| Crashed (w:world).

Arguments Crashed {T} w.

Definition base_step : forall T, baseOpT T -> world -> T -> world -> Prop :=
  IO.base_step baseModel.

Inductive exec : forall T, proc T -> world -> Result T -> Prop :=
| ExecRet : forall T (v:T) w,
    exec (Ret v) w (Finished v w)
| ExecBindFinished : forall T T' (p: proc T) (p': T -> proc T')
                       w v w' r,
    exec p w (Finished v w') ->
    exec (p' v) w' r ->
    exec (Bind p p') w r
| ExecOp : forall T (op: baseOpT T) w v w',
    base_step op w v w' ->
    exec (BaseOp _ op) w (Finished v w')
| ExecCrashBegin : forall T (p: proc T) w,
    exec p w (Crashed w)
| ExecCrashEnd : forall T (p: proc T) w v w',
    exec p w (Finished v w') ->
    exec p w (Crashed w')
| ExecBindCrashed : forall T T' (p: proc T) (p': T -> proc T')
                      w w',
    exec p w (Crashed w') ->
    exec (Bind p p') w (Crashed w').

Definition world_crash : world -> world := IO.world_crash baseModel.

Inductive exec_recover R (rec:proc R) (w:world) : R -> world -> Prop :=
 | ExecRecoverExec : forall v w',
    exec rec w (Finished v w') ->
    exec_recover rec w v w'
 | ExecRecoverCrashDuringRecovery : forall w' v w'',
    exec rec w (Crashed w') ->
    exec_recover rec (world_crash w') v w'' ->
    exec_recover rec w v w''.
