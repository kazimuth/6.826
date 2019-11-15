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

(** Some simple proofs that don't go anywhere else. *)
Section HelperProofs.
  Theorem some_maybe_eq : forall T (t:T) (v:T),
      maybe_eq (Some t) v ->
      t = v.
  Proof.
    intros.
    unfold maybe_eq in H.
    unfold maybe_holds in H.
    intuition.
  Qed.

  Theorem list_cons_app_unit_eq : forall A (l:list A) (a:A),
      a :: l = [a] ++ l.
  Proof.
    easy.
  Qed.

  Lemma app_inv_len : forall A (l1 l1' l2 l2' : list A),
      l1 ++ l1' = l2 ++ l2' ->
      length l1' = length l2' ->
      l1 = l2 /\ l1' = l2'.
  Proof.
    induction l1 as [|x1 l1]; destruct l2 as [|x2 l2].
    { intros. compute in H. intuition. }
    { intros.
      absurd (length (nil ++ l1') = length ((x2 :: l2) ++ l2')).
      - simpl. rewrite app_length. rewrite H0. lia.
      - rewrite H. trivial. }
    { intros.
      absurd (length ((x1 :: l1) ++ l1') = length (nil ++ l2')).
      - simpl. rewrite app_length. rewrite H0. lia.
      - rewrite H. trivial. }
    {
      intros. cut (l1 ++ l1' = l2 ++ l2').
        {
          intros. pose proof (IHl1 l1' l2 l2' H1 H0); intuition.
          apply app_inv_tail in H.
          trivial.
        }
        injection H.
        intros.
        trivial.
    }
  Qed.
End HelperProofs.


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
  (* checking that the list gets appended to in the order i think
     it does... *)
  Example list_order : nth_error ([1; 2; 3]) 0 = Some 1.
  Proof.
    intuition.
  Qed.

  (** A helper to fetch the last entry from the spec: *)
  Definition diskGetLogLength (d : disk) : nat :=
    match diskGet d (diskSize d - 1) with
    | Some v => block_to_addr v
    | None => 0
    end.

  (** Properties of the helper *)
  Section diskGetLogLength_proofs.
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

    Theorem diskGetLogLength_no_upd :
      forall disk q i,
        let size := diskSize disk in
        i < size - 1 ->
        diskGetLogLength (diskUpd disk i q) = diskGetLogLength disk.
    Proof.
      intros.
      unfold diskGetLogLength.
      rewrite -> diskUpd_size.
      unfold size.
      rewrite -> diskUpd_neq by lia.
      trivial.
    Qed.

    Theorem diskGetLogLength_no_upds :
      forall bs disk start,
        let size := diskSize disk in
        start + length bs <= size - 1 ->
        diskGetLogLength (diskUpds disk start bs) = diskGetLogLength disk.
    Proof.
      induction bs as [| x bs']; auto.
      intros.
      simpl.
      rewrite diskGetLogLength_no_upd.
      2: {
        rewrite diskUpds_size.
        assert (length (x :: bs') >= 1).
        { simpl. lia. }
        lia.
      }
      pose proof (@IHbs' disk (start+1)).
      simpl in H.
      rewrite H0; try lia; trivial.
    Qed.
  End diskGetLogLength_proofs.

  (* Helper theorems about diskGets and friends. Proof automation from Disk.v *)
  Section diskGets_proof.

    Hint Rewrite nth_error_app1 using (autorewrite with disk_size in *; lia) : upd.
    Hint Rewrite nth_error_app2 using (autorewrite with disk_size in *; lia) : upd.
    Hint Rewrite diskGets_index using lia : upd.

    Ltac nth_error_intros :=
      intros;
      apply nth_error_ext_inbounds_eq;
      repeat rewrite ?diskGets_length, ?app_length, ?map_length; try lia;
      intros i **;
      autorewrite with disk_size upd in *;
      try rewrite diskGets_index by lia.

    Ltac nth_error_crush a d1 d2 i :=
      destruct (lt_dec i (length d1 - a));
      unfold diskGet;
      autorewrite with disk_size upd in *;
      try auto;
      unfold diskGet;
      do 2 f_equal.

    Theorem diskGets_oob_eq : forall n (s : disk) a,
        a >= diskSize s ->
        diskGets s a n = repeat None n.
    Proof.
      induction n.
      - intros. simpl. congruence.
      - intros. simpl. rewrite disk_oob_eq by lia.
        rewrite IHn by lia. trivial.
    Qed.

    Theorem diskGets_first_S : forall count d a,
        diskGets d a (S count) = diskGet d a :: diskGets d (a+1) count.
    Proof.
      intros.
      reflexivity.
    Qed.

    Theorem diskGets_app_disk_skip : forall d1 d2 a count,
        a >= length d1 ->
        diskGets (d1 ++ d2) a count =
        diskGets d2 (a - length d1) count.
    Proof.
      nth_error_intros.
      nth_error_crush a d1 d2 i.
      lia.
    Qed.

    Theorem diskGets_app_disk_ext : forall d1 d2 a count,
        count < length d1 - a ->
        a < length d1 ->
        diskGets (d1 ++ d2) a count =
        diskGets d1 a count.
    Proof.
      nth_error_intros.
      nth_error_crush a d1 d2 i.
    Qed.

    Theorem diskGets_app_disk_left : forall d1 d2 a count,
        count = length d1 ->
        a = 0 ->
        diskGets (d1 ++ d2) a count =
        diskGets d1 a count.
    Proof.
      nth_error_intros.
      nth_error_crush a d1 d2 i.
    Qed.

    Theorem diskGets_app_disk_right : forall d1 d2 a count,
        count = length d2 ->
        a = length d1 ->
        diskGets (d1 ++ d2) a count =
        diskGets d2 0 count.
    Proof.
      nth_error_intros.
      nth_error_crush a d1 d2 i.
      replace (length d1 + i - length d1) with i by lia.
      lia.
    Qed.

    Lemma diskGets_map_Some_eq : forall (d : disk),
        map Some d = diskGets d 0 (length d).
    Proof.
      induction d.
      - compute. trivial.
      - simpl. replace (a :: d) with ([a] ++ d) by easy.
        rewrite diskGets_app_disk_right; simpl; try lia; congruence.
    Qed.

    Theorem diskGets_lowerchunk : forall (s:addr) (d d':disk) (v:block),
        diskSize d = diskSize d' ->
        diskSize d >= s ->
        diskGets d' 0 (s+1) = diskGets (diskUpd d s v) 0 (s+1) ->
        diskGets d' 0 s = diskGets d 0 s.
    Proof.
      induction s.
      {
        auto.
      }
      {
        intros.
        repeat rewrite diskGets_app in H1.
        replace (S s) with (s + 1) in * by lia.
        rewrite diskUpd_diskGets_neq in H1 by lia.
        apply app_inv_len in H1.
        2: {
          repeat rewrite diskGets_length.
          trivial.
        }
        intuition.
      }
    Qed.

    Theorem diskGets_full_same : forall (d1 d2 : disk),
        diskGets d1 0 (length d1) = diskGets d2 0 (length d2) ->
        d1 = d2.
    Proof.
      induction d1 as [| h1 d1']; destruct d2 as [|h2 d2']; intros;
        simpl in *; auto; try congruence.
      replace (h1 :: d1') with ([h1] ++ d1') in * by easy.
      replace (h2 :: d2') with ([h2] ++ d2') in * by easy.

      repeat rewrite diskGets_app_disk_right in H by easy.
      assert (diskGets d1' 0 (length d1') = diskGets d2' 0 (length d2')).
      { congruence. }
      specialize (IHd1' d2' H0).
      congruence.
    Qed.

  End diskGets_proof.




  (** define the abstraction first, so we can interleave definitions and proofs *)
  Inductive log_abstraction (disk_state : OneDiskAPI.State) (log_state : LogAPI.State) : Prop :=
    (* fun fact: both states are just `list block` *)

    | LogAbstraction :
      let nonsense := 0 in
      forall
        (* maximum log length is (disk size - 1) *)
        (Hlength_inbounds : ((not(diskSize disk_state = 0) -> length log_state < diskSize disk_state)) /\ (diskSize disk_state = 0 -> length log_state = 0))
        (* last entry on disk is the same as log length (or log length is 0) *)
        (Hlength_on_disk : length log_state = diskGetLogLength disk_state)
        (* for all nats i below log length, the block at i on the disk corresponds to the block at i in the log. we use diskGets log_state here even though log_state isn't a disk to ease later
         proofs. *)
        (Hentries : diskGets log_state 0 (length log_state) = diskGets disk_state 0 (length log_state))
      ,
      log_abstraction disk_state log_state.
  Definition abstr : Abstraction State :=
    abstraction_compose d.abstr {| abstraction := log_abstraction |}.
  Hint Constructors log_abstraction : core.

  (* Abstraction checks *)

  Example abstr_1_ok : forall (len2 : block), block_to_addr len2 = 2 ->
log_abstraction ([block0; block1; len2]) ([block0; block1]).
  Proof.
    constructor; eauto; intros; simpl; simpl in *; lia.
  Qed.

  Example abstr_2_ok : forall (len0 : block), block_to_addr len0 = 0 ->
                                         log_abstraction ([block0; block0; len0]) ([]).
  Proof.
    constructor; eauto; intros; simpl; simpl in *; lia.
  Qed.

  Example abstr_3_ok : forall (len2 : block), block_to_addr len2 = 2 ->
                                         log_abstraction ([block0; block1; block0; len2]) ([block0; block1]).
  Proof.
    constructor; eauto; intros; simpl; simpl in *; lia.
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


  (* Helper procedure: get log length from disk. *)
  Definition log_length : proc nat :=
    sz <- d.size;
    if gt_dec sz 0 then
      len <- d.read (sz - 1);
      Ret (block_to_addr len)
    else
      Ret 0.

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

  (* to initialize, just set length to 0. *)
  Definition init' : proc InitResult :=
    sz <- d.size;
    n_ <- addr_to_block 0;
    _ <- d.write (sz - 1) n_;
    Ret Initialized.
  Definition init := then_init d.init init'.
  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'.
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
      compute.
      trivial.
    }
  Qed.

  (*
  a b c d

  a b c d _ _ _ 4
  ^               get_rec 4 4 = a ::
    ^             get_rec 4 3 = b ::
      ^           get_rec 4 2 = c ::
        ^         get_rec 4 1 = d ::
                  get_rec 4 0 = []
   *)

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

  (*
  Definition get_spec : Specification unit (list block) unit State :=
    fun (_ : unit) state => {|
        pre := True;
        post := fun r state' => r = state /\ state' = state;
        recovered := fun _ state' => state' = state
      |}.
   *)
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
      destruct (diskSize state) eqn:Heq; intuition.
      {
        rewrite diskGetLogLength_zero in H2 by lia. simpl in H2. apply map_eq_nil in H2.
        apply length_zero_iff_nil in H0.
        congruence.
      }
      {
        rewrite <- Hlength_on_disk in *.
        replace (length state2 - length state2) with 0 in H2 by lia.
        rewrite <- H2 in Hentries.
        rewrite diskGets_map_Some_eq in Hentries.
        apply diskGets_full_same in Hentries.
        congruence.
      }
    }
    exists state2. intuition.
  Qed.

  (*

   [ a  b  c  d  e  f  g  h  2 ]
        ^
        len         ^
          [q  r  s] end
           ^
           bs


  *)

  (* helper for `append`. note: addr goes up as bs shrinks *)
  Fixpoint append_rec (bs : list block) (end_ : nat) : proc unit :=
    match bs with
    | nil =>
      Ret tt
    | cons b bs_ =>
      _ <- d.write (end_ - length bs) b;
      _ <- append_rec bs_ (end_);
      Ret tt
    end.

  (* note: writes from (end - len bs) to end, exclusive *)
  Theorem append_rec_ok : forall (bs : list block) (end_ : nat) ,
      proc_spec (fun (_ : unit) disk_state =>
                   let len := diskGetLogLength disk_state in
                   let addr := (end_ - length bs) in {|
                     pre := end_ < (diskSize disk_state)
                           /\ end_ > 0
                           /\ length bs <= end_ - len;
                     post := fun _ disk_state' =>
                              disk_state' = diskUpds disk_state addr bs /\
                              diskGetLogLength disk_state' = diskGetLogLength disk_state /\
                              diskSize disk_state' = diskSize disk_state
                     ;
                     recovered := fun _ disk_state' =>
                                   disk_state' = disk_state \/
                                   (* we don't care what gets written as long as their
                                   log entries proper are safe.*)
                                   diskGets disk_state' 0 addr = diskGets disk_state 0 addr /\
                                   diskGetLogLength disk_state = diskGetLogLength disk_state' /\

                                   diskSize disk_state' = diskSize disk_state
                                   ;
      |}) (append_rec bs end_) recover d.abstr.
  Proof.
    induction bs.
    {
      simpl.
      step_proc.
      intuition.
    }
    {
      step_proc.
      {
        destruct H2 as [Hfailed | Hsucceeded].
        {
          intuition.
        }
        {
          right.
          split; intuition.
          {
            rewrite diskUpd_diskGets_neq by lia.
            trivial.
          }
          {
            rewrite diskGetLogLength_no_upd by lia.
            trivial.
          }
          {
            rewrite diskUpd_size.
            trivial.
          }
        }
      }
      step_proc; try rewrite diskUpd_size; try rewrite diskGetLogLength_no_upd; try lia.
      {
        right.
        destruct H2 as [Hnoop | Hmutate].
        {
          split; intuition.
          {
            rewrite diskUpd_diskGets_neq by lia.
            trivial.
          }
          {
            rewrite diskGetLogLength_no_upd by lia.
            trivial.
          }
          {
            rewrite diskUpd_size.
            trivial.
          }
        }
        {
          intuition; rewrite diskUpd_size in H4; rewrite diskGetLogLength_no_upd in H3 by lia; try assumption.
          {
            remember (end_ - S (length bs)) as newstart.
            remember (end_ - length bs) as oldstart.

            destruct (oldstart == newstart).
            {
              rewrite e in H2.
              rewrite diskUpd_diskGets_neq in H2 by lia.
              assumption.
            }
            {
              replace oldstart with (newstart + 1) in * by lia.
              pose proof (@diskGets_lowerchunk newstart state state' a).
              rewrite H5; trivial; intuition. lia.
            }
          }
        }
      }
      step_proc.
      {
        replace (end_ - S (length bs) + 1) with (end_ - length bs).
        2: lia.
        rewrite diskUpds_diskUpd_comm by lia.
        trivial.
      }
      {
        right.
        intuition.
        rewrite diskUpds_diskGets_neq by lia.
        rewrite diskUpd_diskGets_neq by lia.
        trivial.
      }
    }
  Qed.

  Hint Resolve append_rec_ok : core.

  Definition append (bs : list block) : proc bool :=
    size <- d.size;
    len <- log_length;
    if length bs == 0 then
      Ret true
    else if lt_dec (len + length bs) (size-1) then
      _ <- append_rec bs (len + length bs);
      new_len <- addr_to_block (len + length bs);
      _ <- d.write (size - 1) new_len;
      Ret true
    else
      Ret false.
  (*
  Definition append_spec v : Specification unit bool unit State :=
  fun (_ : unit) state => {|
    pre := True;
    post := fun r state' => r = true /\ state' = state ++ v \/
                            r = false /\ state' = state;
    recovered := fun _ state' => state' = state \/ state' = state ++ v
  |}.
  *)

  Theorem append_ok : forall bs, proc_spec (append_spec bs) (append bs) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    step_proc.
    { exists state2. intuition. }
    step_proc.
    { exists state2. intuition. }
    destruct (equal_dec (length bs) 0).
    {
      step_proc.
      {
        apply length_zero_iff_nil in e. exists state2. rewrite e. intuition. left. intuition.
        rewrite <- app_nil_end. trivial.
      }
      {
        apply length_zero_iff_nil in e. exists state2. rewrite e. intuition.
      }
    }
    destruct (lt_dec (r + length bs) (diskSize state - 1)).
    2: {
      step_proc.
      { exists state2. intuition. }
      { exists state2. intuition. }
    }
    (* THE JUICE *)
    step_proc; try intuition; try lia.
    {
      exists state2. intuition.
    }
    {
      exists (state2).
      invert_abstraction.
      intuition.
      constructor.
      {
        intuition; lia.
      }
      {
        rewrite Hlength_on_disk. assumption.
      }
      {
        rewrite <- Hlength_on_disk in *.
        replace (length state2 + length bs - length bs) with (length state2) in H1 by lia.
        congruence.
      }
    }

    (* helper lemma *)
    assert (diskGets (diskUpds state (length state2) bs) 0 (length state2) =
                         diskGets state 0 (length state2)) as Hno_upd_entries.
    { rewrite diskUpds_diskGets_neq by lia; trivial. }

    assert (log_abstraction state [diskGetLogLength state |=> bs] state2) as Hpre_write.
    {
      (* prove the state valid pre-write. *)
      invert_abstraction.
      intuition.
      constructor.
      {
        split.
        {
          intuition. rewrite diskUpds_size. lia.
        }
        {
          intuition. rewrite diskUpds_size in H1. lia.
        }
      }
      {
        rewrite Hlength_on_disk.
        rewrite diskGetLogLength_no_upds by lia.
        trivial.
      }
      {
        congruence.
      }
    }

    step_proc.
    {
      exists state2. intuition.
      replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) by lia.
      assumption.
    }

    assert (block_to_addr r0 = diskGetLogLength state + length bs
            -> log_abstraction
                (state [diskGetLogLength state + length bs - length bs |=> bs]
                       [diskSize state - 1 |-> r0])
                (state2 ++ bs)) as Hpost_write.
    {
      intros.
      invert_abstraction.
      constructor; intros; simpl in *; eauto;
        repeat rewrite diskUpd_size in * by lia;
        repeat rewrite diskUpds_size in * by lia;
        repeat rewrite diskGetLogLength_no_upds in * by lia.
      {
        destruct (diskSize state == 0); intuition; rewrite app_length; lia.
      }
      {
        intuition.
        rewrite app_length.
        unfold diskGetLogLength at 1.
        rewrite -> diskUpd_size.
        rewrite -> diskUpds_size.
        rewrite -> diskUpd_eq.
        2: { rewrite diskUpds_size. lia. }
        lia.
      }
      {
        rewrite app_length.
        rewrite diskUpd_diskGets_neq by lia.
        rewrite <- Hlength_on_disk in *.
        replace (length state2 + length bs - length bs) with (length state2) by lia.
        repeat rewrite diskGets_app.
        rewrite diskGets_app_disk_left by lia.
        rewrite diskGets_app_disk_right by lia.
        rewrite <- Hentries.
        rewrite diskUpds_diskGets_eq by lia.
        rewrite diskGets_map_Some_eq.
        trivial.
      }
    }

    step_proc.
    {
      destruct H as [Hfailed_before | Hfailed_after].
      {
        exists state2.
        intuition.
        replace (diskGetLogLength state + length bs - length bs) with (diskGetLogLength state) by lia.
        assumption.
      }
      {
        (* the write went through. *)
        exists (state2 ++ bs).
        intuition.
      }
    }
    step_proc; exists (state2 ++ bs); intuition.
  Qed.

  Definition reset : proc unit :=
    sz <- d.size;
      n_ <- addr_to_block 0;
      _ <- d.write (sz - 1) n_;
      Ret tt.
  Theorem reset_ok : proc_spec reset_spec reset recover abstr.
  Proof.
    unfold reset.
    apply spec_abstraction_compose; simpl.
    step_proc.
    { exists state2. intuition. }
    step_proc.
    { exists state2. intuition. }
    step_proc.
    {
      destruct H1 as [Hfailed | Hsucceeded].
      {
        exists state2. intuition.
      }
      {
        exists []. intuition.
        destruct (diskSize state) eqn:Heq.
        {
          constructor; invert_abstraction; simpl; auto.
          {
            lia.
          }
          rewrite diskGetLogLength_zero.
          2: {
            rewrite diskUpd_size. assumption.
          }
          trivial.
        }
        {
          constructor; invert_abstraction; simpl; auto.
          {
            lia.
          }
          {
            replace (n - 0) with (diskSize state - 1) by lia.
            rewrite diskGetLogLength_upd by lia.
            intuition.
          }
        }
      }
    }
    assert (log_abstraction state [diskSize state - 1 |-> r] nil).
    {
      intuition.
      destruct (diskSize state) eqn:Heq.
      {
        constructor; invert_abstraction; simpl; auto.
        {
          lia.
        }
        rewrite diskGetLogLength_zero.
        2: {
          rewrite diskUpd_size. assumption.
        }
        trivial.
      }
      {
        constructor; invert_abstraction; simpl; auto.
        {
          lia.
        }
        {
          replace (n - 0) with (diskSize state - 1) by lia.
          rewrite diskGetLogLength_upd by lia.
          intuition.
        }
      }
    }
    step_proc.
    { exists []. intuition. }
    { exists []. intuition. }
  Qed.



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
