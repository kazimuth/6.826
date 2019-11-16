Require Import POCS.

Require Import TwoDiskAPI.
Require Import Common.OneDiskAPI.

(**
ReplicatedDisk provides a single-disk API on top of two disks, handling disk
failures with replication.

Your job will be to implement the core of the recovery procedure for the
replicated disk, and prove that the entire implementation is correct using your
recovery procedure. This lab is split into several parts. Unlike in previous
labs, the exercises do not proceed in order in the file; you'll first write
specifications and admit the correctness proof, and then you'll come back and
finish the proof.
*)

(** TODO:
- what is the relationship between the sizes of the disks?
- theorem: at least one in two_disks_are is ok
*)


(** Stolen Ltac helpers. **)
Ltac destruct_all :=
  repeat match goal with
         | _ => solve [ auto ]
         | [ i: diskId |- _ ] => destruct i
         | [ |- context[match ?s with
                       | BothDisks _ _ => _
                       | OnlyDisk0 _ => _
                       | OnlyDisk1 _ => _
                       end] ] => destruct s
         | _ => simpl in *
         end.

Ltac inv_step :=
  match goal with
  | [ H: op_step _ _ _ _ |- _ ] =>
    inversion H; subst; clear H;
    repeat sigT_eq;
    safe_intuition
  end.

Ltac inv_bg :=
  match goal with
  | [ H: bg_failure _ _ |- _ ] =>
    inversion H; subst; clear H
  end.

Theorem maybe_holds_stable : forall state state' F0 F1,
    disk0 state ?|= F0 ->
    disk1 state ?|= F1 ->
    bg_failure state state' ->
    disk0 state' ?|= F0 /\
    disk1 state' ?|= F1.
Proof.
  intros.
  inv_bg; simpl in *; eauto.
Qed.

Ltac cleanup :=
  repeat match goal with
         | [ |- forall _, _ ] => intros
         | |- _ /\ _ => split; [ solve [ eauto || congruence ] | ]
         | |- _ /\ _ => split; [ | solve [ eauto || congruence ] ]
         | [ H: Working _ = Working _ |- _ ] => inversion H; subst; clear H
         | [ H: bg_failure _ _ |- _ ] =>
           eapply maybe_holds_stable in H;
           [ | solve [ eauto ] | solve [ eauto ] ]; destruct_ands
         | [ H: _ ?|= eq _, H': _ = Some _ |- _ ] =>
           pose proof (holds_some_inv_eq _ H' H); clear H
         | [ H: ?A * ?B |- _ ] => destruct H
         | [ H: DiskResult _ |- _ ] => destruct H
         | _ => deex
         | _ => destruct_tuple
         | _ => progress unfold pre_step in *
         | _ => progress autounfold in *
         | _ => progress simpl in *
         | _ => progress subst
         | _ => progress safe_intuition
         | _ => solve [ eauto ]
         | _ => congruence
         | _ => inv_step
         | H: context[match ?expr with _ => _ end] |- _ =>
           destruct expr eqn:?; [ | solve [ repeat cleanup ] ]
         | H: context[match ?expr with _ => _ end] |- _ =>
           destruct expr eqn:?; [ solve [ repeat cleanup ] | ]
         end.

Ltac prim :=
  intros;
  eapply proc_spec_weaken; [ eauto | unfold spec_impl ]; exists tt;
  intuition eauto; cleanup;
  intuition eauto; cleanup.

Module ReplicatedDisk (td : TwoDiskAPI) <: OneDiskAPI.

  (* EXERCISE (4a): implement read (DONE) *)
  Definition read (a:addr) : proc block :=
    r1 <- td.read d0 a;
    match r1 with
    | Working v => Ret v
    | Failed => (
        r2 <- td.read d1 a;
          match r2 with
          | Working v => Ret v
          | Failed => Ret block0 (* impossible *)
          end
      )
    end.

  Definition write (a:addr) (b:block) : proc unit :=
    _ <- td.write d0 a b;
    _ <- td.write d1 a b;
    Ret tt.

  Definition size : proc nat :=
    msz <- td.size d0;
    match msz with
    | Working sz => Ret sz
    | Failed =>
      msz <- td.size d1;
      match msz with
      | Working sz => Ret sz
      | Failed => Ret 0
      end
    end.

  (** [sizeInit] computes the size during initialization; it may return None if
  the sizes of the underlying disks differ. *)
  Definition sizeInit : proc (option nat) :=
    sz1 <- td.size d0;
    sz2 <- td.size d1;
    match sz1 with
    | Working sz1 =>
      match sz2 with
      | Working sz2 =>
        if sz1 == sz2 then Ret (Some sz1) else Ret None
      | Failed => Ret (Some sz1)
      end
    | Failed =>
      match sz2 with
      | Working sz2 => Ret (Some sz2)
      | Failed => Ret None
      end
    end.

  (* Recursively initialize block a and below. For simplicity, we make the disks
  match by setting every block to [block0]. *)
  Fixpoint init_at (a:nat) : proc unit :=
    match a with
    | 0 => Ret tt
    | S a =>
      _ <- td.write d0 a block0;
      _ <- td.write d1 a block0;
      init_at a
    end.

  (* Initialize every disk block *)
  Definition init' : proc InitResult :=
    size <- sizeInit;
    match size with
    | Some sz =>
      _ <- init_at sz;
      Ret Initialized
    | None =>
      Ret InitFailed
    end.

  Definition init := then_init td.init init'.


  (**
   * Helper theorems and tactics for proofs.
   *)

  Theorem exists_tuple2 : forall A B (P: A * B -> Prop),
      (exists a b, P (a, b)) ->
      (exists p, P p).
  Proof.
    intros.
    repeat deex; eauto.
  Qed.

  (* The [simplify] tactic performs a number of steps that should simplify and
  clean up your goals. *)
  Ltac simplify :=
    repeat match goal with
           | |- forall _, _ => intros
           | _ => deex
           | _ => destruct_tuple
           | [ u: unit |- _ ] => destruct u
           | |- _ /\ _ => split; [ solve [auto] | ]
           | |- _ /\ _ => split; [ | solve [auto] ]
           | |- exists (_: disk*_), _ => apply exists_tuple2
           | _ => progress simpl in *
           | _ => progress safe_intuition
           | _ => progress subst
           | _ => progress autorewrite with upd in *
           end.

  (* The [finish] tactic tries a number of techniques to solve the goal. *)
  Ltac finish :=
    repeat match goal with
           | _ => solve_false
           | _ => congruence
           | _ => solve [ intuition ]
           | _ =>
             (* if we can solve all the side conditions automatically, then it's
             safe to run descend and create existential variables *)
             descend; (intuition eauto);
             lazymatch goal with
             | |- proc_spec _ _ _ _ => idtac
             | _ => fail
             end
           end.

  Ltac step :=
    step_proc; simplify; finish.

  (**
   * Specifications and proofs about our implementation of the replicated disk API,
   * without considering our recovery.
   *
   * These intermediate specifications separate reasoning about the
   * implementations from recovery behavior.
   *)

  Theorem both_disks_not_missing : forall (state: TwoDiskBaseAPI.State),
      two_disks_are state missing missing ->
      False.
  Proof.
    unfold two_disks_are.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve both_disks_not_missing : false.

  Theorem missing0_implies_any : forall (state: TwoDiskBaseAPI.State) P F,
      two_disks_are state missing F ->
      two_disks_are state P F.
  Proof.
    unfold two_disks_are.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Theorem missing1_implies_any : forall (state: TwoDiskBaseAPI.State) P F,
      two_disks_are state F missing ->
      two_disks_are state F P.
  Proof.
    unfold two_disks_are.
    destruct state; unfold missing; simpl; intuition auto.
  Qed.

  Hint Resolve missing0_implies_any : core.
  Hint Resolve missing1_implies_any : core.

  (* EXERCISE (4a): prove this specification for read (DONE) *)
  Theorem read_int_ok : forall a,
      proc_spec
        (fun d state =>
           {|
             pre := two_disks_are state (eq d) (eq d);
             post :=
               fun r state' =>
                 two_disks_are state' (eq d) (eq d) /\
                 diskGet d a =?= r;
             recovered :=
               fun _ state' =>
                 two_disks_are state' (eq d) (eq d);
           |})
        (read a)
        td.recover
        td.abstr.
  Proof.
    unfold read.
    step.
    repeat (destruct r; step).
  Qed.

  Hint Resolve read_int_ok : core.

  (* EXERCISE (4a): complete and prove this specification for write (DONE) *)
  Theorem write_int_ok : forall a b,
      proc_spec
        (fun d state =>
           {|
             pre := two_disks_are state (eq d) (eq d);
             post :=
               fun r state' =>
                 r = tt /\
                 two_disks_are state' (eq (diskUpd d a b)) (eq (diskUpd d a b));
             recovered :=
               fun _ state' =>
                 (* EXERCISE (4a): write the recovered condition for write. Note
                 that this is the two-disk API's recovery, not the replicated
                 disk's recovery, so it should cover all the crash cases for
                 write *)
                 two_disks_are state' (eq d) (eq d) \/
                 two_disks_are state' (eq (diskUpd d a b)) (eq d) \/
                 two_disks_are state' (eq (diskUpd d a b)) (eq (diskUpd d a b))
             ;
           |})
        (write a b)
        td.recover
        td.abstr.
  Proof.
    unfold write.
    step.
    repeat (destruct r; step).
  Qed.

  Hint Resolve write_int_ok : core.

  (* EXERCISE (4a): prove this specification for size (DONE) *)
  Theorem size_int_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {|
           pre := two_disks_are state (eq d_0) (eq d_1) /\
             diskSize d_0 = diskSize d_1;
           post :=
             fun r state' =>
               r = diskSize d_0 /\
               r = diskSize d_1 /\
               two_disks_are state' (eq d_0) (eq d_1);
           recovered :=
             fun _ state' =>
               two_disks_are state' (eq d_0) (eq d_1);
         |})
      (size)
      td.recover
      td.abstr.
  Proof.
    unfold size.
    step.
    repeat (destruct r; step).
  Qed.

  Hint Resolve size_int_ok : core.

  (* We provide a proof for [init]. *)

  Definition equal_after a (d_0 d_1: disk) :=
    diskSize d_0 = diskSize d_1 /\
    forall a', a <= a' -> diskGet d_0 a' = diskGet d_1 a'.

  Theorem le_eq_or_S_le : forall n m,
      n <= m ->
      n = m \/
      S n <= m /\ n <> m.
  Proof.
    intros.
    lia.
  Qed.

  Theorem equal_after_diskUpd : forall a d_0 d_1 b,
      equal_after (S a) d_0 d_1 ->
      equal_after a (diskUpd d_0 a b) (diskUpd d_1 a b).
  Proof.
    unfold equal_after; intuition.
    - autorewrite with upd; eauto.
    - apply le_eq_or_S_le in H1; intuition subst.
      { destruct (lt_dec a' (diskSize d_0)); autorewrite with upd.
        + assert (a' < diskSize d_1) by congruence; autorewrite with upd; auto.
        + assert (~a' < diskSize d_1) by congruence; autorewrite with upd; auto.
      }
      autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_diskUpd : core.

  Theorem init_at_ok : forall a,
      proc_spec
        (fun '(d_0, d_1) state =>
           {| pre :=
                two_disks_are state (eq d_0) (eq d_1) /\
                equal_after a d_0 d_1;
              post :=
                fun _ state' =>
                  exists d_0' d_1': disk,
                    two_disks_are state' (eq d_0') (eq d_1') /\
                    equal_after 0 d_0' d_1';
              recovered :=
                fun _ state' => True;
           |})
        (init_at a)
        td.recover
        td.abstr.
  Proof.
    induction a; simpl; intros.
    - step.
    - step.
      step.
      destruct r; finish.
      + step.
        destruct r; simplify; finish.
      + step.
        destruct r; simplify.
        * exists (diskUpd d_0 a block0).
          exists (diskUpd d_1 a block0).
          finish.
        * finish.
  Qed.

  Hint Resolve init_at_ok : core.

  Theorem sizeInit_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {| pre :=
              two_disks_are state (eq d_0) (eq d_1);
            post :=
              fun r state' =>
                exists d_0' d_1',
                  two_disks_are state' (eq d_0') (eq d_1') /\
                  match r with
                  | Some sz => diskSize d_0' = sz /\ diskSize d_1' = sz
                  | None => True
                  end;
            recovered :=
              fun _ state' => True;
         |})
      (sizeInit)
      td.recover
      td.abstr.
  Proof.
    unfold sizeInit.
    step.
    destruct r.
    - step.
      destruct r.
      + destruct (diskSize d_0 == v).
        * step.
        * step.
      + step.
    - step.
      destruct r.
      + step.
      + step.
  Qed.

  Hint Resolve sizeInit_ok : core.


  Theorem equal_after_0_to_eq : forall d_0 d_1,
      equal_after 0 d_0 d_1 ->
      d_0 = d_1.
  Proof.
    unfold equal_after; intuition.
    eapply disk_ext_eq; intros.
    eapply H0; lia.
  Qed.

  Theorem equal_after_size : forall d_0 d_1,
      diskSize d_0 = diskSize d_1 ->
      equal_after (diskSize d_0) d_0 d_1.
  Proof.
    unfold equal_after; intuition.
    assert (~a' < diskSize d_0) by lia.
    assert (~a' < diskSize d_1) by congruence.
    autorewrite with upd; eauto.
  Qed.

  Hint Resolve equal_after_size : core.
  Hint Resolve equal_after_0_to_eq : core.

  Theorem init'_ok :
    proc_spec
      (fun '(d_0, d_1) state =>
         {| pre :=
              two_disks_are state (eq d_0) (eq d_1);
            post :=
              fun r state' =>
                match r with
                | Initialized =>
                  exists d_0' d_1',
                  two_disks_are state' (eq d_0') (eq d_1') /\
                  d_0' = d_1'
                | InitFailed =>
                  True
                end;
            recovered :=
              fun _ state' => True;
         |})
      (init')
      td.recover
      td.abstr.
  Proof.
    unfold init'.
    step.
    destruct r; step.
    step.
  Qed.

  Hint Resolve init'_ok : core.

  (**
   * Recovery implementation.
   *
   * We provide the general structure for recovery: essentially, it consists of
   * a loop around [fixup] that terminates after either fixing an out-of-sync
   * disk block or when a disk has failed.
  *)

  (* [fixup] returns a [RecStatus] to implement early termination in [recovery_at]. *)
  Inductive RecStatus :=
  (* continue working, nothing interesting has happened *)
  | Continue
  (* some address has been repaired (or the recovery has exhausted the
     addresses) - only one address can be out of sync and thus only it must be
     recovered. *)
  (* OR, one of the disks has failed, so don't bother continuing recovery since
     the invariant is now trivially satisfied *)
  | RepairDoneOrFailed.

  (* EXERCISE (4c): implement [fixup], which should perform recovery for a
  single address and indicate whether to continue or not. (DONE) *)
  Definition fixup (a:addr) : proc RecStatus :=
    r0 <- td.read d0 a;
    match r0 with
      | Failed => Ret RepairDoneOrFailed
      | Working r0 =>
          r1 <- td.read d1 a;
            match r1 with
            | Failed => Ret RepairDoneOrFailed
            | Working r1 =>
              if r0 == r1 then
                Ret Continue
              else
                _ <- td.write d1 a r0;
                Ret RepairDoneOrFailed
            end
    end.

  (* recursively performs recovery at [a-1], [a-2], down to 0 *)
  Fixpoint recover_at (a:addr) : proc unit :=
    match a with
    | 0 => Ret tt
    | S n =>
      vv <- fixup n;
      match vv with
      | Continue => recover_at n
      | RepairDoneOrFailed => Ret tt
      end
    end.

  Definition Recover : proc unit :=
    sz <- size;
    _ <- recover_at sz;
    Ret tt.


  (**
   * Theorems and recovery proofs.
   *)

  Theorem if_lt_dec : forall A n m (a a':A),
      n < m ->
      (if lt_dec n m then a else a') = a.
  Proof.
    intros.
    destruct (lt_dec n m); auto.
  Qed.

  Theorem disks_eq_inbounds : forall (d: disk) a v v',
      a < diskSize d ->
      diskGet d a =?= v ->
      diskGet d a =?= v' ->
      v = v'.
  Proof.
    intros.
    case_eq (diskGet d a); intros.
    - rewrite H2 in *. simpl in *. congruence.
    - exfalso.
      eapply disk_inbounds_not_none; eauto.
  Qed.

  (* To make these specifications precise while also covering both the already
   * synced and diverged disks cases, we keep track of which input state we're
   * in from the input and use it to give an exact postcondition. *)
  Inductive DiskStatus :=
  | FullySynced
  | OutOfSync (a:addr) (b:block).

  Theorem diskUpd_maybe_same : forall (d:disk) a b,
      diskGet d a =?= b ->
      diskUpd d a b = d.
  Proof.
    intros.
    destruct (diskGet d a) eqn:?; simpl in *; subst;
      autorewrite with upd;
      auto.
  Qed.

  Hint Rewrite diskUpd_maybe_same using (solve [ auto ]) : upd.
  Hint Resolve PeanoNat.Nat.lt_neq : core.
  Hint Resolve disks_eq_inbounds : core.

  Definition both_disks_live state :=
    match state with
    | BothDisks _ _ => True
    | _ => False
    end.

  Definition some_disk_dead state :=
    match state with
    | BothDisks _ _ => False
    | _ => True
    end.

  Definition death_permanent state state' :=
    match state with
    | BothDisks _ _ => True
    | OnlyDisk0 _ => match state' with
                  | OnlyDisk0 _ => True
                  | _ => False
                  end
    | OnlyDisk1 _ => match state' with
                  | OnlyDisk1 _ => True
                  | _ => False
                  end
    end.

  Theorem death_permanent_refl : forall state,
    death_permanent state state.
  Proof.
    intros. destruct state; simpl; trivial.
  Qed.

  Hint Resolve death_permanent_refl : core.

  (* EXERCISE (4c): write and admit a specification for [fixup]. (DONE) *)
  Theorem fixup_ok : forall a,
      proc_spec
        ((fun '(d, s) state =>
           {|
             pre :=
               a < diskSize d /\
               match s with
               | FullySynced => two_disks_are state (eq d) (eq d)
               | OutOfSync a' b => two_disks_are state (eq (diskUpd d a' b)) (eq d) /\
                                  both_disks_live state /\
                                  (diskUpd d a' b) <> d
               end;
             post :=
               fun r state' =>
                 match s with
                 | FullySynced =>
                   two_disks_are state' (eq d) (eq d)
                 | OutOfSync a' b =>
                   if a == a' then
                     r = RepairDoneOrFailed /\
                     (two_disks_are state' (eq (diskUpd d a' b)) (eq (diskUpd d a' b)) \/
                       (* disk 0 failed concurrently during recovery *)
                       state' = OnlyDisk1 d)
                   else
                     (r = Continue /\ two_disks_are state' (eq (diskUpd d a' b)) (eq d)) \/
                     (r = RepairDoneOrFailed /\
                      match state' with
                      | BothDisks _ _ => False
                      | OnlyDisk0 disk0 => disk0 = diskUpd d a' b
                      | OnlyDisk1 disk1 => disk1 = d
                      end)
                 end;
             recovered :=
               fun _ state' =>
                 match s with
                 | FullySynced => two_disks_are state' (eq d) (eq d)
                 | OutOfSync a' b =>
                   if a == a' then
                     (two_disks_are state' (eq (diskUpd d a' b)) (eq (diskUpd d a' b))) \/
                     two_disks_are state' (eq (diskUpd d a' b)) (eq d)
                   else
                     two_disks_are state' (eq (diskUpd d a' b)) (eq d)
                 end;
           |}) : (prod disk DiskStatus) -> _ -> _)
        (fixup a)
        td.recover
        td.abstr.
  Proof.
    (* EXERCISE (4d): prove [fixup_ok] (DONE) *)
    intros.
    step.
    destruct s.
    {
      (* Fully synced. *)
      exists d, (eq d).
      intuition.
      destruct r as [r|]; step.
      - destruct r0 as [r0|].
        + destruct (equal_dec r r0); step.
        + step.
    }
    {
      (* Not synced. *)
      exists (diskUpd d a0 b), (eq d).
      intuition.
      - destruct (equal_dec a a0); intuition.
      - destruct r as [r|]; step.
        + exists d, (eq (diskUpd d a0 b)); destruct (a == a0); intuition;
          destruct r0 as [r0|]; try destruct (r == r0); step.
          (* OH GOD SO MANY CASES *)
          { step; destruct r; intuition. }
          destruct state1; intuition; unfold two_disks_are in H5; simpl in H5; intuition.
        + destruct (a == a0); intuition; unfold two_disks_are in H3; simpl in H3;
            destruct state0; compute in H3; intuition.
        + destruct (a == a0); intuition.
    }
  Qed.

  Hint Resolve fixup_ok : core.

  Hint Resolve Lt.lt_n_Sm_le : core.

  Definition DEBUG_POST_CONDITION := True.
  Definition DEBUG_RECOVER_CONDITION := True.

  (*
             post :=
               fun r state' =>
                 match s with
                 | FullySynced =>
                   two_disks_are state' (eq d) (eq d)
                 | OutOfSync a' b =>
                   if a == a' then
                     r = RepairDoneOrFailed /\
                     (two_disks_are state' (eq (diskUpd d a' b)) (eq (diskUpd d a' b)) \/
                       (* disk 0 failed concurrently during recovery *)
                       state' = OnlyDisk1 d)
                   else
                     (r = Continue /\ two_disks_are state' (eq (diskUpd d a' b)) (eq d)) \/
                     (r = RepairDoneOrFailed /\
                      match state' with
                      | BothDisks _ _ => False
                      | OnlyDisk0 disk0 => disk0 = diskUpd d a' b
                      | OnlyDisk1 disk1 => disk1 = d
                      end)

             post :=
               fun _ state' =>
                 DEBUG_POST_CONDITION /\
                 match s with
                 | FullySynced => two_disks_are state' (eq d) (eq d)
                 | OutOfSync a' b =>
                   if lt_dec a' a then
                     two_disks_are state' (eq (diskUpd d a' b)) (eq (diskUpd d a' b)) \/
                     state' = OnlyDisk1 d
                   else
                     two_disks_are state' (eq (diskUpd d a' b)) (eq d)
                 end;

  *)

  (* EXERCISE (4c): specify and prove recover_at *)
  (* Hint: use [induction a] *)

  Theorem recover_at_ok_ : forall a,
      proc_spec
        (fun '(_:unit) state =>
           {|
             pre := True;
             post := fun _ state' => True;
             recovered := fun _ state' => True;
           |})
        (recover_at a)
        td.recover
        td.abstr.
  Proof.
    induction a; unfold recover_at.

  Qed.

  (* recover goes down; the base case is the bottom of the disk.
     we need to show that, if the borked block was below the current iteration,
     it has been stamped out.
   *)
  Theorem recover_at_ok : forall a,
      proc_spec
        (fun '(d, s) state =>
           {|
             pre :=
               a < diskSize d /\
               match s with
               | FullySynced => two_disks_are state (eq d) (eq d)
               | OutOfSync a' b => two_disks_are state (eq (diskUpd d a' b)) (eq d) /\
                                  both_disks_live state /\
                                  ((diskUpd d a' b) <> d)
               end;
             post :=
               fun _ state' =>
                 DEBUG_POST_CONDITION /\
                 match s with
                 | FullySynced => two_disks_are state' (eq d) (eq d)
                 | OutOfSync a' b =>
                   if lt_dec a' a then
                     two_disks_are state' (eq (diskUpd d a' b)) (eq (diskUpd d a' b)) \/
                     state' = OnlyDisk1 d
                   else
                     two_disks_are state' (eq (diskUpd d a' b)) (eq d) \/
                      match state' with
                      | BothDisks _ _ => False
                      | OnlyDisk0 disk0 => disk0 = diskUpd d a' b
                      | OnlyDisk1 disk1 => disk1 = d
                      end
                 end;
             recovered :=
               fun _ state' =>
                 DEBUG_RECOVER_CONDITION /\
                 match s with
                 | FullySynced => two_disks_are state' (eq d) (eq d)
                 | OutOfSync a' b =>
                   if lt_dec a' a then
                     (two_disks_are state' (eq (diskUpd d a' b)) (eq (diskUpd d a' b))) \/
                     two_disks_are state' (eq (diskUpd d a' b)) (eq d)
                   else
                     two_disks_are state' (eq (diskUpd d a' b)) (eq d)
                 end;
           |})
        (recover_at a)
        td.recover
        td.abstr.
  Proof.
    induction a; unfold recover_at.

    {
      (* base case: straightforward *)
      unfold DEBUG_RECOVER_CONDITION in *; unfold DEBUG_POST_CONDITION in *.
      step; destruct s; intuition.
    }

    (* inductive case. *)

    (* call fixup. *)
    step.

    (* check the ghost variables. *)
    destruct s.
    {
      (* We're fully synced. Everything is straightforward. *)
      exists d, FullySynced.
      unfold DEBUG_RECOVER_CONDITION in *; unfold DEBUG_POST_CONDITION in *.
      intuition; simplify.
      destruct r; step.
      exists d, FullySynced.
      intuition; simplify.
    }
    {
      (* We're out of sync! *)

      (* Our initial state must have been BothDisks. *)
      destruct state; simpl in H0; intuition.

      (* Show fixup's preconditions hold. *)
      exists d, (OutOfSync a0 b).

      intuition; simplify.
      {
        unfold DEBUG_RECOVER_CONDITION in *; unfold DEBUG_POST_CONDITION in *;
        destruct (lt_dec a0 (S a)); destruct (equal_dec a a0); simplify.
      }
      {
        unfold DEBUG_RECOVER_CONDITION in *; unfold DEBUG_POST_CONDITION in *;
        destruct (lt_dec a0 (S a)); destruct (equal_dec a a0); simplify.
      }

      (* What did fixup return? *)
      destruct r.
      {
        (* fixup returned Continue. *)

        (* make the recursive call to recover_at. *)
        step.

        (* this is useless now. *)
        clear IHa.

        (* a != a0, because fixup returned Continue.*)
        destruct (equal_dec a a0).
        { intuition; discriminate. }

        (* our update process is incomplete (at this step),
           because fixup returned Continue *)
        destruct H1.
        2: {
          intuition. discriminate.
        }

        (* clean up hypotheses. *)
        intuition.

        (* destruct the state after recursive call to recover_at. *)
        destruct state.
        {
          (* Both disks live after recover_at *)
          unfold two_disks_are in H0. simpl in H0.
          unfold two_disks_are in H3. simpl in H3.
          intuition.
          exists d_3, (OutOfSync a0 b).
          intuition.
          {
            unfold two_disks_are. simpl. intuition.
          }
          {
            simpl. trivial.
          }
          {
            destruct (lt_dec a0 (S a)); destruct (lt_dec a0 a); try lia; intuition.
          }
          {
            destruct (lt_dec a0 (S a)); destruct (lt_dec a0 a); try lia; intuition.
          }
        }
        {
          (* Only disk 0 live after recover_at *)
          unfold two_disks_are in H0. simpl in H0.
          unfold two_disks_are in H3. simpl in H3.
          intuition.

          (* the ghost variables input to recover_at: *)
          exists (diskUpd d_1 a0 b), FullySynced.

          split.
          {
            (* preconditions *)
            intuition.
            - rewrite diskUpd_size. lia.
            - unfold two_disks_are. simpl. intuition.
          }
          split.
          {
            (* postconditions *)
            unfold DEBUG_RECOVER_CONDITION in *; unfold DEBUG_POST_CONDITION in *.
            intuition.
            destruct (lt_dec a0 (S a)).
            {
              intuition.
            }
            {
              destruct state'.
              {
                admit.
              }
              {
                unfold two_disks_are in *.
                simpl in *.
                intuition.
              }
              {
                unfold two_disks_are in *.
                simpl in *.
                intuition.
              }

            }

            (* state' must be OnlyDisk1 *)
            destruct state'.
            {

            }

            admit.
          }
          {
            (* recovery conditions *)
            admit.
          }
        }
        admit.
      }
      {
        (* fixup returned RepairDoneOrFailed. *)
        step_proc; clear IHa;
          unfold DEBUG_RECOVER_CONDITION in *; unfold DEBUG_POST_CONDITION in *;
            try trivial.
        {
          destruct (lt_dec a0 (S a)); destruct (equal_dec a a0); intuition;
            try lia; try discriminate; destruct state; try contradiction;
              rewrite <- H3; unfold two_disks_are; simpl; intuition.
        }
        {
          unfold DEBUG_RECOVER_CONDITION in *; unfold DEBUG_POST_CONDITION in *;
          destruct (lt_dec a0 (S a)); destruct (equal_dec a a0); intuition;
            unfold two_disks_are in *; simplify; destruct state; simplify.
        }
      }
    }
  Qed.

  Hint Resolve recover_at_ok : core.

  (* EXERCISE (4b): write a spec for recovery (DONE) *)
  Definition Recover_spec : Specification _ unit unit TwoDiskBaseAPI.State :=
    fun '(d, a, v) state =>
      (* note: you can just put a out of bounds
         if you don't need the write.*)
      let d' := diskUpd d a v in
      {|
        pre := two_disks_are state (eq d') (eq d') \/ two_disks_are state (eq d') (eq d);
        post := fun _ state' => two_disks_are state' (eq d') (eq d');
        recovered := fun _ state' => two_disks_are state' (eq d') (eq d') \/ two_disks_are state' (eq d') (eq d);
      |}.

  (* EXERCISE (4c): prove recovery correct *)
  Theorem Recover_rok :
    proc_spec
      Recover_spec
      (Recover)
      td.recover
      td.abstr.
  Proof.
  Admitted.

  (* EXERCISE (4b): prove that your recovery specification is idempotent; that
  is, its recovered condition implies its precondition. (DONE) *)
  Theorem Recover_spec_idempotent :
    idempotent Recover_spec.
  Proof.
    unfold idempotent.
    intuition; simplify.
    exists a.
    destruct a as [a b].
    destruct a as [d a].
    simpl in *.
    intuition.
  Qed.

  (* This proof combines your proof that recovery is correct and that its
  specification is idempotent to show recovery is correct even if re-run on
  every crash. *)
  Theorem Recover_ok :
    proc_loopspec
      Recover_spec
      (Recover)
      td.recover
      td.abstr.
  Proof.
    eapply idempotent_loopspec; simpl.
    - apply Recover_rok.
    - apply Recover_spec_idempotent.
  Qed.

  Hint Resolve Recover_ok : core.

  Definition recover: proc unit :=
    _ <- td.recover;
    Recover.

  (* As the final step in giving the correctness of the replicated disk
  operations, we prove recovery specs that include the replicated disk Recover
  function. *)

  Definition rd_abstraction (state: TwoDiskBaseAPI.State) (d:OneDiskAPI.State) : Prop :=
    two_disks_are state (eq d) (eq d).

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose td.abstr {| abstraction := rd_abstraction; |}.

  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    intros.
    eapply then_init_compose; eauto.
    eapply proc_spec_weaken; eauto.
    unfold spec_impl; intros.
    destruct state; simpl in *.

    - exists (d_0, d_1); simpl; intuition.
      { unfold two_disks_are; simpl; intuition. }
      unfold rd_abstraction.
      destruct v; simplify; finish.
    - exists (d_0, d_0); simplify; intuition.
      { unfold two_disks_are; simpl; intuition. }
      unfold rd_abstraction.
      destruct v; simplify; finish.
    - exists (d_1, d_1); simplify; finish; intuition.
      { unfold two_disks_are; simpl; intuition. }
      unfold rd_abstraction.
      destruct v; simplify; finish.
  Qed.

  (* EXERCISE (4b): prove that read, write, and size are correct when combined
  with your recovery (using your specification but admitted proof). (DONE) *)

  Definition recover_ghost_noop (state : disk) :=
    (state, diskSize state, block0).

  Ltac exists_recover_ghost_noop state :=
      exists (recover_ghost_noop state);
      simpl;
      rewrite diskUpd_oob_noop by lia.

  Theorem read_ok : forall a, proc_spec (read_spec a) (read a) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    eapply compose_recovery; eauto; simplify.
    unfold rd_abstraction in H0.
    exists state2.
    simplify.
    split.
    {
      intros.
      exists state2.
      simplify.
    }
    {
      intros.
      exists_recover_ghost_noop state2.
      intuition.
      exists state2.
      intuition.
    }
  Qed.

  Theorem write_ok : forall a v, proc_spec (write_spec a v) (write a v) recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    eapply compose_recovery; eauto; simplify.
    unfold rd_abstraction in *.
    intuition.
    exists state2. intuition.
    (* post *)
    { exists (diskUpd state2 a v). intuition. }
    (* recovery: no write *)
    { exists_recover_ghost_noop state2. intuition. exists state2. intuition. }
    all: (exists (state2, a, v); simpl; intuition;
             exists (diskUpd state2 a v); intuition).
  Qed.

  Theorem size_ok : proc_spec size_spec size recover abstr.
  Proof.
    intros.
    apply spec_abstraction_compose; simpl.
    (* simplify is a bit too aggressive about existential variables here, so we
    provide some manual simplification here *)
    eapply compose_recovery; eauto.
    intros; apply exists_tuple2.
    destruct a; simpl in *.
    exists s. exists s.
    unfold rd_abstraction in H.
    intuition.
    - exists s. intuition.
    - exists_recover_ghost_noop s. intuition. exists s. intuition.
  Qed.

  (* This theorem shows that Ret does not modify the abstract state exposed by
  the replicated disk; the interesting part is that if recovery runs, then the
  only effect should be the wipe relation (the trivial relation [no_wipe] in
  this case) *)
  (* EXERCISE (4b): prove this theorem using your recovery spec (DONE) *)
  Theorem recover_wipe : rec_wipe recover abstr no_wipe.
  Proof.
    eapply rec_wipe_compose; eauto; simpl.
    autounfold; unfold rd_abstraction, Recover_spec; simplify.
    exists_recover_ghost_noop state0'.
    intuition.
    exists state0'.
    intuition.
  Qed.

End ReplicatedDisk.
