Require Import POCS.
Require Import LogAPI.
Require Import Common.OneDiskAPI.
Import ListNotations.

(** * Implementation of the atomic append-only log. *)

(** Your job is to implement the atomic append-only log API,
    as defined in [LogAPI.v], on top of a single disk, as
    defined in [OneDiskAPI.v].  The underlying disk is the
    same abstraction that you implemented in lab 2.

    To achieve crash-safety, you can rely on the fact that
    the underlying disk provides atomic block writes: that
    is, writing to a single disk block is atomic with respect
    to crash-safety.  If the system crashes in the middle of
    a write to a disk block, then after the crash, that block
    has either the old value or the new value, but not some
    other corrupted value.

    The disk provided by [OneDiskAPI.v] is synchronous, in
    the sense that disk writes that have fully completed (where
    [write] returned) are durable: if the computer crashes after
    a [write] finished, that [write] will still be there after
    the computer reboots. *)

(** To implement the log API, we assume that we have a procedure
    [addr_to_block] that encodes a number as a block, and a way
    to read the number back from the block (the function
    [block_to_addr]). This gives your implementation a way to
    serialize data onto disk. *)

Axiom addr_to_block : addr -> proc block.
Axiom block_to_addr : block -> addr.

Definition addr_to_block_spec State a : Specification unit block unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => state' = state /\ block_to_addr r = a;
    recovered := fun _ state' => state' = state
  |}.
Axiom addr_to_block_ok : forall State a recover abstr,
  proc_spec (@addr_to_block_spec State a) (addr_to_block a) recover abstr.
Hint Resolve addr_to_block_ok : core.


(** For this lab, we provide a notation for diskUpd. Not only can you use this
    to write [diskUpd d a b] as [d [a |-> b]] but you will also see this notation
    in goals. This should especially make it easier to read goals with many
    updates of the same disk.

    Remember that the code still uses diskUpd underneath, so the same theorems
    apply. We recommend using [autorewrite with upd] or [autorewrite with upd
    in *] in this lab to simplify diskGet/diskUpd expressions, rather than
    using the theorems manually. *)
Notation "d [ a |-> b ]" := (diskUpd d a b) (at level 8, left associativity).
Notation "d [ a |=> bs ]" := (diskUpds d a bs) (at level 8, left associativity).

Opaque diskGet.


(** In this lab, you will likely be doing reasoning about
    the contents of various disk blocks.  The following
    theorem will help you do so. *)
Theorem diskGet_eq_values : forall d a b b',
    diskGet d a =?= b ->
    diskGet d a =?= b' ->
    a < diskSize d ->
    b = b'.
Proof.
  (* Fill in your proof here. *)
Admitted.

(** We use the above theorem to implement the [eq_values]
    tactic.  [eq_values] can be used when you have hypotheses
    like:

        H1: diskGet d a =?= eq b
        H2: diskGet d a =?= eq b'

    In this context, the tactic proves b = b'.
 *)
Ltac eq_values :=
  match goal with
  | [ H:  diskGet ?d ?a =?= ?b,
      H': diskGet ?d ?a =?= ?b' |- _ ] =>
    assert (b = b') by (apply (@diskGet_eq_values d a b b'); try lia; auto);
    subst
  end.


Module Log (d : OneDiskAPI) <: LogAPI.

  (** Fill in your implementation and proof here, replacing
      the placeholder statements below with your own definitions
      and theorems as appropriate.  Feel free to introduce helper
      procedures and helper theorems to structure your implementation
      and proof. *)

  Definition init : proc InitResult := Ret Initialized.
  Definition get : proc (list block) := Ret nil.
  Definition append (bs : list block) : proc bool := Ret true.
  Definition reset : proc unit := Ret tt.
  Definition recover : proc unit := Ret tt.

  Axiom abstr : Abstraction State.
  Axiom init_ok : init_abstraction init recover abstr inited_any.
  Axiom get_ok : proc_spec get_spec get recover abstr.
  Axiom append_ok : forall v, proc_spec (append_spec v) (append v) recover abstr.
  Axiom reset_ok : proc_spec reset_spec reset recover abstr.
  Axiom recover_wipe : rec_wipe recover abstr no_wipe.


End Log.


(** It's possible to layer the log from this lab on top
    of the bad-block remapper from the previous lab.
    The statements below do that, just as a sanity check.
  *)

Require Import Lab2.BadBlockImpl.
Require Import Lab2.RemappedDiskImpl.
Module bad_disk := BadBlockDisk.
Module remapped_disk := RemappedDisk bad_disk.
Module log := Log remapped_disk.
Print Assumptions log.append_ok.
