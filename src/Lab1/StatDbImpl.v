Require Import POCS.
Require Import VariablesAPI.
Require Import StatDbAPI.

(** * An implementation of StatDB

   StatDB is built on top of the Variables API, which maintains two variables
   [VarCount] and [VarSum]. StatDB reads and writes these two variables using
   the API provided in the VarsAPI module. [VarCount] stores the number of
   integers that [VarSum] sums up. The mean is just [VarSum]/[VarCount].

  *)


Module StatDB (v : VarsAPI) <: StatDbAPI.

  Import ListNotations.

  Definition add (v : nat) : proc unit :=
    sum <- v.read VarSum;
    count <- v.read VarCount;
    _ <- v.write VarSum (sum + v);
    _ <- v.write VarCount (count + 1);
    Ret tt.

  (** ** Exercise : complete the implementation of mean *)
  Definition mean : proc (option nat) :=
    sum <- v.read VarSum;
    count <- v.read VarCount;
    match count with
    | 0 => Ret None
    | S n => Ret (Some (sum / S n))
    end.

  Definition init' : proc InitResult :=
    _ <- v.write VarCount 0;
    _ <- v.write VarSum 0;
    Ret Initialized.

  Definition init := then_init v.init init'.

  Definition recover : proc unit :=
    v.recover.

  (** ** Exercise : complete the implementation of the abstraction function: *)
  Definition statdb_abstraction (vars_state : VariablesAPI.State) (statdb_state : StatDbAPI.State) : Prop :=
    (StateCount vars_state = length statdb_state) /\ (StateSum vars_state = fold_right plus 0 statdb_state).

  Definition abstr : Abstraction StatDbAPI.State :=
    abstraction_compose
      v.abstr
      {| abstraction := statdb_abstraction |}.

  Example abstr_1_ok : statdb_abstraction (VariablesAPI.mkState 1 3) [3].
  Proof.
    unfold statdb_abstraction; simpl.
    lia. (* this works for our abstraction relation *)
  Qed.

  (** ** Exercise : complete the proof for the following admitted examples *)
  Example abstr_2_ok : statdb_abstraction (VariablesAPI.mkState 2 3) [1; 2].
  Proof.
    unfold statdb_abstraction; simpl.
    lia.
  Qed.

  Example abstr_3_ok : statdb_abstraction (VariablesAPI.mkState 0 0) nil.
  Proof.
    unfold statdb_abstraction. simpl. lia.
  Qed.

  Example abstr_4_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) [2].
  Proof.
    unfold statdb_abstraction; simpl.
    lia.
  Qed.

  Example abstr_5_nok : ~ statdb_abstraction (VariablesAPI.mkState 1 0) nil.
  Proof.
    unfold statdb_abstraction; simpl.
    lia.
  Qed.

  Theorem init_ok : init_abstraction init recover abstr inited.
  Proof.
    eapply then_init_compose; eauto.
    unfold init'.

    step_proc.
    step_proc.
    step_proc.
    exists nil.
    unfold statdb_abstraction, inited.
    intuition.
  Qed.

  (** ** Exercise : complete the proof of [add] *)
  Theorem add_ok : forall v, proc_spec (add_spec v) (add v) recover abstr.
  Proof.
    unfold add.
    intros.

    apply spec_abstraction_compose; simpl.
    unfold statdb_abstraction.
    step_proc.
    { contradiction. }
    step_proc.
    { contradiction. }
    step_proc.
    { contradiction. }
    step_proc.
    { contradiction. }
    step_proc.
    {
      exists (v :: state2).
      simpl.
      rewrite -> H0.
      rewrite -> H1.
      intuition.
      {
        lia.
      }
      {
        lia.
      }
    }
    contradiction.
  Qed.

  Opaque Nat.div.

  (** ** Exercise : complete the proof of [mean] *)
  Theorem mean_ok : proc_spec mean_spec mean recover abstr.
  Proof.
    unfold mean.
    intros.

    apply spec_abstraction_compose; simpl.
    unfold statdb_abstraction.

    step_proc.
    { contradiction. }
    step_proc.
    { contradiction. }
    destruct r as [| n].
    {
      step_proc.
      {
        rewrite H0.
        rewrite H1.
        exists state2. simpl.
        rewrite <- H3 in H0.
        symmetry in H0.
        rewrite -> length_zero_iff_nil in H0.
        repeat rewrite H0. simpl. intuition.
      }
      {
        contradiction.
      }
    }
    {
      step_proc.
      {
        rewrite H0.
        rewrite H1.
        exists state2.
        intuition.
        right.
        split.
        {
          intuition.
          assert (H' := H0).
          rewrite <- H3 in H'.
          discriminate.
        }
        {
          rewrite H3.
          rewrite H0.
          reflexivity.
        }
      }
      {
        contradiction.
      }
    }

  Qed.


  Theorem recover_wipe : rec_wipe recover abstr no_crash.
  Proof.
    unfold rec_wipe.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc.
    { exists state2. eauto. }
    { exfalso. eauto. }
  Qed.

End StatDB.


Require Import VariablesImpl.
Module StatDBImpl := StatDB Vars.
Print Assumptions StatDBImpl.abstr_2_ok.
Print Assumptions StatDBImpl.abstr_3_ok.
Print Assumptions StatDBImpl.abstr_4_nok.
Print Assumptions StatDBImpl.abstr_5_nok.
Print Assumptions StatDBImpl.add_ok.
Print Assumptions StatDBImpl.mean_ok.
