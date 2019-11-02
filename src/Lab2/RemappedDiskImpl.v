Require Import POCS.
Require Import OneDiskAPI.
Require Import BadBlockAPI.


Module RemappedDisk (bd : BadBlockAPI) <: OneDiskAPI.

  Import ListNotations.

  Definition read (a : addr) : proc block :=
    bs <- bd.getBadBlock;
    if a == bs then
      len <- bd.size;
      r <- bd.read (len-1);
      Ret r
    else
      r <- bd.read a;
      Ret r.

  Definition write (a : addr) (b : block) : proc unit :=
    bs <- bd.getBadBlock;
    len <- bd.size;
    if a == bs then
      _ <- bd.write (len-1) b;
      Ret tt
    else
      if a == (len-1) then
        Ret tt
      else
        _ <- bd.write a b;
        Ret tt.

  Definition size : proc nat :=
    len <- bd.size;
    Ret (len - 1).

  Definition init' : proc InitResult :=
    len <- bd.size;
    if len == 0 then
      Ret InitFailed
    else
      bs <- bd.getBadBlock;
      if (lt_dec bs len) then
        Ret Initialized
      else
        Ret InitFailed.

  Definition init := then_init bd.init init'.

  Definition recover: proc unit :=
    bd.recover.

  Inductive remapped_abstraction (bs_state : BadBlockAPI.State) (rd_disk : OneDiskAPI.State) : Prop :=
    | RemappedAbstraction :
      let bs_disk := stateDisk bs_state in
      let bs_addr := stateBadBlock bs_state in
      forall
        (* Fill in the rest of your abstraction here. *)
        (* To refer to the contents of disk [d] at address [a], you can write [diskGet d a] *) (* <-- TODO this was wrong*)
        (* To refer to the size of disk [d], you can write [diskSize d] *)
        (* You can try to prove [read_ok] to discover what you need from this abstraction *)

        (* Hint 1: What should be true about the non-bad blocks?   Replace [True] with what needs to be true *)
        (Hgoodblocks : forall a : nat, (a < diskSize rd_disk /\ not(a = bs_addr)) -> diskGet bs_disk a = diskGet rd_disk a)
        (* Hint 2: What should be true about the bad block? *)
        (Hbadblock : (bs_addr < diskSize rd_disk) -> diskGet rd_disk bs_addr = diskGet bs_disk (diskSize bs_disk - 1))

        (* when writing the above,  *)
        (* Hint 3: What if the bad block address is the last address? *)
        (Hsize : diskSize bs_disk = diskSize rd_disk + 1),
      remapped_abstraction bs_state rd_disk.

  Hint Constructors remapped_abstraction : core.

  Definition abstr : Abstraction OneDiskAPI.State :=
    abstraction_compose bd.abstr {| abstraction := remapped_abstraction |}.

  (* Note that these examples aren't trivial to prove, even if you have the
     right abstraction relation. They should help you think about whether your
     abstraction relation makes sense (although you may need to modify it to
     actually prove the implementation correct). *)

  Example abst_1_ok : forall Hinbounds,
    remapped_abstraction (BadBlockAPI.mkState [block1;block0;block0] 0 Hinbounds) [block0;block0].
  Proof.
    constructor; auto.
    simpl. intros.
    assert (a = 1).
    {
      lia.
    }
    intuition.
  Qed.

  Example abst_2_ok : forall Hinbounds,
    remapped_abstraction (BadBlockAPI.mkState [block1;block0] 0 Hinbounds) [block0].
  Proof.
    constructor; auto.
    simpl. intros.
    absurd (a < 1 /\ a <> 0).
    + lia.
    + apply H.
  Qed.

  Example abst_3_ok : forall Hinbounds,
    remapped_abstraction (BadBlockAPI.mkState [block0;block0] 1 Hinbounds) [block0].
  Proof.
    constructor; auto.
    - simpl. intuition.
      assert (a = 0).
      {
        lia.
      }
      intuition.
    - simpl. intuition. absurd (1 < 1).
      + lia.
      + apply H.
  Qed.

  (*Unset Printing Notations.*)

  Lemma some_eq : forall a b : block, Some a = Some b -> a = b.
  Proof.
    intros.
    injection H. trivial.
  Qed.

  Example abst_4_nok : forall Hinbounds,
    ~ remapped_abstraction (BadBlockAPI.mkState [block0;block0] 1 Hinbounds) [block1].
  Proof.
    intros.
    intro.
    inversion H. simpl in *.
    specialize (Hgoodblocks 0).
    unfold bs_addr in Hgoodblocks.
    simpl in Hgoodblocks. intuition.
    apply some_eq in Hgoodblocks.
    apply bytes_differ in Hgoodblocks.
    { contradiction. }
    unfold blockbytes. lia.
  Qed.

  Example abst_5_nok : forall Hinbounds,
    ~ remapped_abstraction (BadBlockAPI.mkState [block1;block1] 0 Hinbounds) [block0].
  Proof.
    intros.
    intro.
    inversion H; simpl in *.
    unfold bs_addr in Hbadblock.
    intuition.
    apply some_eq in Hbadblock.
    apply bytes_differ in Hbadblock.
    { contradiction. }
    unfold blockbytes.
    simpl. lia.
  Qed.

  (* Due to how remapped_abstraction is defined (as an inductive), it cannot be
  unfolded. This tactic identifies abstraction relations in the hypotheses and
  breaks them apart with [inversion], and also does some cleanup. *)
  Ltac invert_abstraction :=
    match goal with
    | H : remapped_abstraction _ _ |- _ => inversion H; clear H; subst; subst_var
    end.


  Theorem init_ok : init_abstraction init recover abstr inited_any.
  Proof.
    eapply then_init_compose; eauto.
    step_proc.
    destruct r as [| n].
    { simpl. step_proc. }
    simpl.
    step_proc.
    destruct (lt_dec r (S n)).
    {
      simpl. step_proc.
      exists (let bs_disk := stateDisk state in
         let bs_addr := stateBadBlock state in
         let shrunk := diskShrink bs_disk in
         let replaced := match diskGet bs_disk n with
                                               | None => block0
                                               | Some a => a
                                               end in
         diskUpd shrunk bs_addr replaced
        ).
      intuition.

      simpl.

      constructor.

      {
        intros.
        destruct H0.

        assert (a0 < diskSize (stateDisk state) - 1).
        {
          rewrite diskUpd_size in H0.
          rewrite diskShrink_size in H0.
          2: {
            rewrite <- H1. lia.
          }
          assumption.
        }

        rewrite <- diskShrink_preserves.
        2: {
          rewrite diskShrink_size.
          2: {
            rewrite <- H1. lia.
          }
          lia.
        }

        rewrite -> diskUpd_neq.
        2: {
          lia.
        }
        trivial.
      }
      {
        intros.
        rewrite diskUpd_size in H0.
        rewrite diskShrink_size in H0.
        2: {
          rewrite <- H1. lia.
        }

        rewrite -> diskUpd_eq.
        2: {
          rewrite diskShrink_size.
          2: {
            rewrite <- H1. lia.
          }
          lia.
        }
        assert (n = diskSize (stateDisk state) - 1).
        { lia. }

        assert (forall (z : nat) (r : block) (d : disk), z < diskSize d -> Some (match diskGet d z with
                                       | Some q => q
                                       | None => r
                                       end) = diskGet d z
               ).
        {
          intros.
          edestruct (diskGet d z) eqn:Heq.
          {
            trivial.
          }
          {
            apply disk_inbounds_not_none in Heq.
            2: { trivial. }
            contradiction.
          }
        }
        rewrite <- H2.
        apply H3.
        lia.
      }
      {
        rewrite diskUpd_size.
        rewrite diskShrink_size; lia.
      }
    }
    {
      step_proc.
    }
  Qed.

Theorem bad_block_inbounds :
    forall state,
      stateBadBlock state < diskSize (stateDisk state).
  Proof.
    intros.
    destruct state.
    simpl.
    exact stateBadBlockInBounds.
  Qed.



  Theorem read_ok : forall a, proc_spec (OneDiskAPI.read_spec a) (read a) recover abstr.
  Proof.
    unfold read.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; eauto.

    destruct (a == r) eqn:Heq1.
    {

      step_proc.
      {
       exists state2. intuition.
      }
      step_proc.
      {
        exists state2. intuition.
      }
      step_proc; intuition.
      {
        exists state2. intuition.
        invert_abstraction.

        destruct (diskSize (stateDisk state) - 1 == stateBadBlock state).
        {
          (* bad block is out of bounds of spec; so diskGet spec bad_block is none.
           so any maybe_eq statement about it is true. *)
          assert (diskGet state2 (stateBadBlock state) = None).
          {
            rewrite <- e.
            rewrite -> Hsize.

            rewrite -> disk_oob_eq.
            2: {
              lia.
            }
            trivial.
          }
          unfold maybe_eq.
          apply holds_in_none_eq.
          assumption.
        }
        {
          (* bad block is not out of bounds. *)
          rewrite <- Hbadblock in H2.
          {
            apply H2 in n.
            assumption.
          }

          assert (stateBadBlock state < diskSize (stateDisk state)).
          {
            apply bad_block_inbounds.
          }
          lia.
        }
      }
      {
        exists state2. intuition.
      }
    }
    step_proc.
    {
      exists state2. intuition.
    }
    step_proc.
    {
      exists state2. intuition.
      invert_abstraction.
      case (lt_dec a (diskSize state2)); intros.
      {
        rewrite <- Hgoodblocks.
        2: {
          intuition.
        }
        assumption.
      }
      {
        assert (diskGet state2 a = None).
        {
          apply disk_oob_eq.
          assumption.
        }
        unfold maybe_eq.
        apply holds_in_none_eq.
        assumption.
      }
    }
    exists state2. intuition.
  Qed.

  (* Hint: you may find it useful to use the [pose proof (bad_block_inbounds state)]
     if you need [lia] to make use of the fact that the bad block is in-bounds. *)

  Theorem remapped_abstraction_diskUpd_remap : forall state state' s v_,
    remapped_abstraction state s ->
    stateBadBlock state' = stateBadBlock state ->
    stateDisk state' = diskUpd (stateDisk state) (diskSize (stateDisk state) - 1) v_ ->
    remapped_abstraction state' (diskUpd s (stateBadBlock state) v_).
  Proof.
    (*
      given a state,
      if we update the last slot,
      that maps to updating the bad block in the spec.
     *)
    intros.
    constructor.
    {
      (* proving Hgoodblocks. *)
      intros. intuition.
      invert_abstraction.
      rewrite -> H0 in H3.
      rewrite -> diskUpd_size in H2.
      rewrite -> H1.
      repeat rewrite -> diskUpd_neq by lia.
      apply Hgoodblocks.
      intuition.
    }
    {
      (* proving Hbadblock. *)
      intros.
      rewrite -> H0.
      rewrite -> H0 in H2.
      rewrite -> diskUpd_size in H2.
      rewrite -> H1.
      rewrite -> diskUpd_size.
      invert_abstraction.
      repeat rewrite -> diskUpd_eq by lia.
      trivial.
    }
    {
      (* proving Hsize. *)
      rewrite -> H1.
      rewrite diskUpd_size.
      rewrite diskUpd_size.
      invert_abstraction.
      assumption.
    }
  Qed.


  Theorem remapped_abstraction_diskUpd_noremap : forall state state' s a v_,
    remapped_abstraction state s ->
    a <> diskSize (stateDisk state) - 1 ->
    a <> stateBadBlock state ->
    stateBadBlock state' = stateBadBlock state ->
    stateDisk state' = diskUpd (stateDisk state) a v_ ->
    remapped_abstraction state' (diskUpd s a v_).
  Proof.
    (*
      given a state, and an address that is neither the bad block
      nor the final block, updating the address is equivalent to updating
      the spec.
     *)
    intros. constructor.
    {
      (* Proving Hgoodblocks. *)
      intros. intuition.
      rewrite -> H2 in H5.
      rewrite -> diskUpd_size in H4.
      rewrite -> H3.
      invert_abstraction.
      case (equal_dec a a0).
      {
        intros.
        rewrite <- e.
        repeat rewrite diskUpd_eq by lia.
        trivial.
      }
      {
        intros.
        repeat rewrite diskUpd_neq by lia.
        apply Hgoodblocks.
        lia.
      }
    }
    {
      (* Proving Hbadblock. *)
      intros.
      rewrite -> H2 in H4.
      rewrite -> H2.
      rewrite -> H3.
      invert_abstraction.
      rewrite -> diskUpd_size.
      repeat rewrite diskUpd_neq by lia.
      apply Hbadblock.
      rewrite diskUpd_size in H4.
      assumption.
    }
    {
      (* Hsize. *)
      rewrite -> H3.
      rewrite diskUpd_size.
      rewrite diskUpd_size.
      invert_abstraction.
      assumption.
    }

  Qed.


  Hint Resolve remapped_abstraction_diskUpd_remap : core.
  Hint Resolve remapped_abstraction_diskUpd_noremap : core.

  Theorem write_ok : forall a v_, proc_spec (OneDiskAPI.write_spec a v_) (write a v_) recover abstr.
  Proof.
    unfold write.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc.
    {
      exists state2. intuition.
    }
    case (equal_dec a r) as [Hwrite_bad | Hwrite_other].
    {
      step_proc.
      {
        exists state2. intuition.
      }
      step_proc.
      {
        destruct H1 as [Hcrash_before | Hcrash_after].
        {
          exists state2. intuition.
        }
        {
          exists (diskUpd state2 (stateBadBlock state) v_). intuition.
        }
      }
      step_proc.
      {
        exists (diskUpd state2 (stateBadBlock state) v_). intuition.
      }
      exists (diskUpd state2 (stateBadBlock state) v_). intuition.
    }
    {
      step_proc.
      {
        exists state2. intuition.
      }
      case (equal_dec a (r - 1)) as [Hwrite_silly | Hwrite_nonsilly].
      {
        step_proc.
        {
          exists state2. intuition.
          invert_abstraction.
          rewrite Hsize.
          rewrite diskUpd_none.
          2: {
            rewrite -> disk_oob_eq by lia.
            trivial.
          }
          trivial.
        }
        {
          exists state2. intuition.
        }
      }
      {
        step_proc.
        {
          destruct H1 as [Hcrash_before | Hcrash_after].
          {
           exists state2. intuition.
          }
          {
            exists (diskUpd state2 a v_).
            intuition.
            eauto.
          }
        }
        step_proc.
        {
          exists (diskUpd state2 a v_). intuition. eauto.
        }
        {
          exists (diskUpd state2 a v_). intuition. eauto.
        }
      }
    }
  Qed.


  Theorem size_ok : proc_spec OneDiskAPI.size_spec size recover abstr.
  Proof.
    unfold diskSize.
    intros.

    apply spec_abstraction_compose; simpl.

    step_proc; eauto.
    step_proc.
    {
      exists state2. intuition.
      invert_abstraction.
      rewrite -> Hsize. lia.
    }
    {
      exists state2. intuition.
    }
  Qed.

  (* This proof proves that recovery corresponds to no_wipe. *)
  Theorem recover_wipe : rec_wipe recover abstr no_wipe.
  Proof.
    unfold rec_wipe.
    intros.

    apply spec_abstraction_compose; simpl.
    step_proc; eauto.
  Qed.

End RemappedDisk.


Require Import BadBlockImpl.
Module x := RemappedDisk BadBlockDisk.
Print Assumptions x.write_ok.
