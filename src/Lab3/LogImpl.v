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


(* from https://sympa.inria.fr/sympa/arc/coq-club/2014-02/msg00157.html *)

(** In this lab, you will likely be doing reasoning about
    the contents of various disk blocks.  The following
    theorem will help you do so. *)
Theorem diskGet_eq_values : forall d a b b',
    diskGet d a =?= b ->
    diskGet d a =?= b' ->
    (* note: you need this condition because in the None case =?= always holds *)
    a < diskSize d ->
    b = b'.
Proof.
  intros.

  assert (diskGet d a = Some b).
  {
    destruct (diskGet d a) eqn:Heq.
    {
      apply holds_in_some in H.
      simpl in H.
      intuition.
    }
    {
      apply disk_inbounds_not_none in H1. 2: assumption.
      contradiction.
    }
  }
  rewrite -> H2 in *.
  intuition.
Qed.

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

  (** spec

    The log provides three operations: [get], [append], and [reset].
    The [get] retrieves all of the blocks currently in the log.

    [append] adds blocks to the log.  The [append] is the most interesting
    part of the log, because [append] must be atomic with respect to crashes.
    That means that, if the system crashes in the middle of an [append],
    either all of the (APPENDED) blocks should be present (i.e., returned by [get]),
    or none of them should be present.

    [append] returns a boolean to indicate whether it succeeded
    or not.  The intent is that [append] might fail if the log
    has grown too big on disk, and there's no room for the new
    blocks.

    Finally, [reset] logically clears the log, removing all entries.  This
    also must be crash-safe: if the system crashes in the middle of clearing
    the log, either the log contents should still be there, or the log should
    appear to be empty (according to [get]).
 *)

  (** disk guarantees (from OneDiskAPI)

    no preconditions, any disk state is valid.

    size_spec: size returns the correct value.
    read_spec: read returns the correct value if the read is in-bounds.
    write_spec:
      post: the disk has been updated correctly.
      recovered: either the write went through to the disk, or it didn't.
 *)

  (** useful definitions

    Definition addr := nat.
    Definition disk := list block

    Axiom diskGet (d : disk) (a : addr) : option block.
    Axiom diskSize (d : disk) : nat := length d.
    Axiom diskUpd d (a: addr) b : disk.
    Axiom diskGets (d : disk) (a : addr) (count : nat) : list (option block).
    Axiom diskUpds (d : disk) (a : addr) (blocks : list block) : disk.

    Specification A T R State: A specification with
        ghost variables A,
        return type T,
        recovery type R,
        state type State.
    It has members:
       pre: Prop,
       post: T -> State -> Prop,
       recovered: R -> State -> Prop.
    It is constructed with a set of ghost variables and a starting state.
 *)

  (** hints
      It seems like proving examples of your abstraction relation can be impossible because
      diskGet is opaque and so it doesn't simplify, even on a disk which is an explicit list
      of blocks. You can remove the line Opaque diskGet. to get around this problem (it was
      jkintended to protect your proofs from unfolding the definition; feel free to add it
      back after proving the examples, or don't use it if you don't run into issues.)

      The examples in this lab will require that you start with an encoded block, but
      there's no function from a number to a block encoding that number. You can work around
      this by proving your examples for an arbitrary block that encodes some number, say
      forall block_2, block_to_addr block_2 = 2 -> .... You also might want to use some
      arbitrary data blocks b1, b2, etc in your examples rather than just combinations of
      block0 and block1.

      You code will need to use recursion, and therefore your proofs will use induction.
      You saw some examples of this way back in lab 0, so I encourage you to go see
      what you did there.
   *)

  (** implementation sketch

    data layout:
      last entry: log length
      other entries: log elements
   *)

  (** helpers *)
  Definition diskGetLogLength (d : disk) : nat :=
    match diskGet d (diskSize d - 1) with
    | Some v => block_to_addr v
    | None => 0
    end.

  Theorem diskGetLogLength_zero :
    forall disk,
    diskSize disk = 0 -> diskGetLogLength disk = 0.
  Proof.
    intros.
    unfold diskGetLogLength.
    rewrite -> H.
    assert (0 - 1 = 0) by lia.
    rewrite -> H0.
    rewrite -> disk_oob_eq by lia.
    trivial.
  Qed.

  Theorem diskGetLogLength_upd :
    forall disk len,
      let size := diskSize disk in
    not(size = 0) -> diskGetLogLength (diskUpd disk (size-1) len) = block_to_addr len.
  Proof.
    intros.
    unfold diskGetLogLength.
    rewrite -> diskUpd_size.
    unfold size.
    rewrite -> diskUpd_eq by lia.
    trivial.
  Qed.

  (* checking that the list gets appended to in the order i think
     it does... *)
  Example list_order : nth_error ([1; 2; 3]) 0 = Some 1.
  Proof.
    intuition.
  Qed.


  (** define the abstraction first, so we can interleave definitions and proofs *)

  Inductive log_abstraction (disk_state : OneDiskAPI.State) (log_state : LogAPI.State) : Prop :=
    (* fun fact: both states are just `list block` *)

    | LogAbstraction :
      let nonsense := 0 in
      forall
        (* maximum log length is (disk size - 1) *)
        (Hlength_inbounds : not(diskSize disk_state = 0) -> length log_state < diskSize disk_state)
        (* last entry on disk is the same as log length (or log length is 0) *)
        (Hlength_on_disk : length log_state = diskGetLogLength disk_state)
        (* for all nats i below log length, the block at i on the disk corresponds to the block at i in the log. *)
        (Hentries : forall i : nat, i < length log_state -> diskGet disk_state i = nth_error log_state i)
      ,
      log_abstraction disk_state log_state.
  Definition abstr : Abstraction State :=
    abstraction_compose d.abstr {| abstraction := log_abstraction |}.
  Hint Constructors log_abstraction : core.

  Example abstr_1_ok : forall (len2 : block), block_to_addr len2 = 2 ->
log_abstraction ([block0; block1; len2]) ([block0; block1]).
  Proof.
    constructor; eauto; intros; simpl; simpl in *.
    destruct (i == 0); intuition.
    destruct (i == 1); intuition.
    lia.
  Qed.

  Example abstr_2_ok : forall (len0 : block), block_to_addr len0 = 0 ->
                                         log_abstraction ([block0; block0; len0]) ([]).
  Proof.
    constructor; eauto; intros; simpl; simpl in *; lia.
  Qed.

  Example abstr_3_ok : forall (len2 : block), block_to_addr len2 = 2 ->
                                         log_abstraction ([block0; block1; block0; len2]) ([block0; block1]).
  Proof.
    constructor; eauto; intros; simpl; simpl in *.
    {
      lia.
    }
    destruct (i == 0); intuition.
    destruct (i == 1); intuition.
    lia.
  Qed.


  (* Recovery is a noop. *)
  Definition recover : proc unit := d.recover.
  (* This proof proves that recovery corresponds to no_wipe. *)
  Theorem recover_wipe : rec_wipe recover abstr no_wipe.
  Proof.
    unfold rec_wipe.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; eauto.
  Qed.

  (* Due to how remapped_abstraction is defined (as an inductive), it cannot be
  unfolded. This tactic identifies abstraction relations in the hypotheses and
  breaks them apart with [inversion], and also does some cleanup. *)
  Ltac invert_abstraction :=
    match goal with
    | H : log_abstraction _ _ |- _ => inversion H; clear H; subst; subst_var
    end.


  (* Helper: get log length from disk. *)
  Definition log_length : proc nat :=
    sz <- d.size;
    if gt_dec sz 0 then
      len <- d.read (sz - 1);
      Ret (block_to_addr len)
    else
      Ret 0.

  (* question: how would we prove this w.r.t. disk state? *)
  Definition log_length_spec : Specification unit nat unit OneDiskAPI.State :=
    fun (_ : unit) disk_state => {|
        pre := True;
        post := fun len disk_state' =>
                 disk_state' = disk_state /\
                 diskGetLogLength disk_state = len;
        recovered := fun _ disk_state' =>
                      disk_state' = disk_state
      |}.
  Theorem log_length_ok : proc_spec log_length_spec log_length recover d.abstr. (* note: we use d.abstr to only prove w.r.t. the disk, not the
    log. *)
    unfold log_length. intros.
    step_proc.
    destruct (gt_dec r 0).
    {
      (* len > 0 *)
      step_proc.
      step_proc.
      unfold diskGetLogLength.
      destruct (diskGet state (diskSize state - 1)) eqn:Heq.
      2: {
        (* can't be none if r > 0 *)
        apply disk_inbounds_not_none in Heq.
        2: lia.
        contradiction.
      }
      assert (b = r) by intuition.
      intuition.
    }
    {
      (* len = 0 *)
      step_proc.
      apply diskGetLogLength_zero.
      lia.
    }
  Qed.

  Hint Resolve log_length_ok : core.


  (* question: how would we prove this w.r.t. disk state? *)
  Definition log_length_hl_spec : Specification unit nat unit LogAPI.State :=
    fun (_ : unit) state => {|
        pre := True;
        post := fun r state' =>
                 state' = state /\
                 length state = r;
        recovered := fun _ state' =>
                      state' = state
      |}.
  Theorem log_length_hl_ok : proc_spec log_length_hl_spec log_length recover abstr.
  Proof.
    apply spec_abstraction_compose; simpl.
    step_proc.
    {
      exists state2. intuition.
      invert_abstraction.
      assumption.
    }
    exists state2. intuition.
  Qed.

  (* we don't prove anything about set_log_length; just handle it in proofs. *)
  Definition set_log_length (n : nat): proc unit :=
    sz <- d.size;
    n_ <- addr_to_block n;
    _ <- d.write (sz - 1) n_;
    Ret tt.


  (* to initialize, just set length to 0. *)
  Definition init' : proc InitResult :=
    _ <- set_log_length 0;
    Ret Initialized.
  Definition init := then_init d.init init'.
  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'. unfold set_log_length.
    step_proc.
    step_proc.
    step_proc.
    step_proc.
    exists nil. intuition.
    constructor.
    {
      (* the length is in bounds. *)
      simpl.
      rewrite -> diskUpd_size.
      lia.
    }
    {
      (* either the disk is size 0, or the log length is set.
       diskGetLogLength is correct in both cases. *)
      simpl.
      destruct (diskSize state == 0).
      {
        rewrite -> diskGetLogLength_zero.
        2: {
          rewrite -> diskUpd_size. assumption.
        }
        trivial.
      }
      {
        rewrite diskGetLogLength_upd by assumption.
        rewrite H1.
        trivial.
      }
    }
    {
      (* log entries are correct: vacuously true for []. *)
      intros.
      simpl in H0.
      assert (i < 0 -> False).
      {
        lia.
      }
      contradiction.
    }
  Qed.

  (*
  (* like set (a:=b) except introduces a name and hypothesis *)
  Tactic Notation
         "provide_name" ident(n) "=" constr(v)
         "as" simple_intropattern(H) :=
    assert (exists n, n = v) as [n H] by (exists v; reflexivity).

  Tactic Notation
         "induction_eqn" ident(n) "as" simple_intropattern(HNS)
         "eqn:" ident(Hn) :=
    let PROP := fresh in (
      pattern n;
      match goal with [ |- ?FP _ ] => set ( PROP := FP ) end;
      induction n as HNS;
      match goal with [ |- PROP ?nnn ] => provide_name n = nnn as Hn end;
      unfold PROP in *; clear PROP
    ).
*)

  Theorem eq_if_maybe_holds_is_some : forall T (p:T -> Prop) mt t,
      maybe_holds p mt ->
      mt = Some t ->
      p t.
  Proof.
    intros.
    unfold maybe_holds in H.
    rewrite H0 in H.
    assumption.
  Qed.

  Theorem eq_if_maybe_eq_is_some : forall T (mt : option T) t v,
      maybe_eq mt t ->
      mt = Some v ->
      Some t = Some v.
  Proof.
    intros.
    unfold maybe_eq in H.
    unfold maybe_holds in H.
    rewrite H0 in H.
    intuition.
  Qed.

  Definition extract T (start : nat) (len : nat) (l : list T) :=
    firstn len (skipn (start - len) l).


  (* helper for `get`. note: addr goes up as remaining goes down *)
  Fixpoint get_rec (len : nat) (remaining : nat) : proc (list block) :=
    match remaining with
    | 0 =>
      Ret nil
    | S remaining_ =>
      b <- d.read (len - (S remaining_));
        rest <- get_rec len remaining_;
        Ret (b :: rest)
    end.
  Theorem get_rec_ok : forall (len:nat) (remaining:nat),
      proc_spec (fun (_ : unit) disk_state => {|
        pre := len <= diskSize disk_state /\ remaining <= len;
        post := fun blocks disk_state' =>
                 disk_state' = disk_state /\
                 (* diskGets returns a list of options >:( *)
                 map Some blocks = diskGets disk_state (len-remaining) (remaining)
                 ;
        recovered := fun _ disk_state' =>
                      disk_state' = disk_state
      |}) (get_rec len remaining) recover d.abstr.
  Proof.
    intros.
    induction remaining as [|remaining'].
    {
      unfold get_rec.
      step_proc.
    }
    {
      step_proc.
      step_proc.
      {
        lia.
      }
      step_proc.
      clear Lexec. clear Lexec0.
      rewrite H3.

      (* prove that reads can't go out of bounds. *)
      assert (diskGet state (len - S remaining') = Some r).
      {
        destruct (diskGet state (len - S remaining')) eqn:Heq.
        {
          unfold maybe_eq in H2.
          unfold maybe_holds in H2.
          intuition.
        }
        {
          apply disk_inbounds_not_none in Heq.
          2: {
            apply disk_none_oob in Heq.
            lia.
          }
          contradiction.
        }
      }

      rewrite H1.
      assert (len - S remaining' + 1 = len - remaining').
      {
        lia.
      }
      rewrite H4.
      trivial.
    }
  Qed.

  Hint Resolve get_rec_ok : core.

  Definition get : proc (list block) :=
    len <- log_length;
    r <- get_rec len len;
    Ret r.
  Theorem get_ok : proc_spec get_spec get recover abstr.
  Proof.
    apply spec_abstraction_compose; simpl.

    unfold get.
    step_proc.
    { exists state2. intuition. }
    step_proc.
    {
      invert_abstraction.
      rewrite Hlength_on_disk in Hlength_inbounds.
      destruct (diskSize state) eqn:Heq.
      {
        rewrite diskGetLogLength_zero by assumption.
        lia.
      }
      {
        lia.
      }
    }
    {
      exists state2. intuition.
    }
    step_proc.
    {
      exists state2. intuition.
      invert_abstraction.
      Search diskGets.
    }

    step_proc_basic.
    intros.
    exists tt.
    intuition.

    step_proc.
    {
      admit.
    }
    {
      admit.
    }
    {
      exists state2. intuition.
    }
    step_proc.
    {
      exists state2. intuition.
    }
    unfold get_rec.
    intro.
    intros.
    induction remaining.
    step_proc.
    step_proc.

    step_proc_basic.


  (* helper for `get`. note: addr goes up as bs shrinks *)
  Fixpoint append_rec (addr : nat) (bs : list block) : proc unit :=
    match bs with
    | nil =>
      Ret tt
    | cons b bs_ =>
      _ <- d.write addr b;
      _ <- append_rec (S addr) bs_;
      Ret tt
    end.
  Definition append (bs : list block) : proc bool :=
    size <- d.size;
    len <- log_length;
    if lt_dec (len + length bs) size then
      _ <- append_rec len bs;
      Ret true
    else
      Ret false.
  Axiom append_ok : forall v, proc_spec (append_spec v) (append v) recover abstr.

  Definition reset : proc unit :=
    _ <- set_log_length 0;
    Ret tt.
  Axiom reset_ok : proc_spec reset_spec reset recover abstr.


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
