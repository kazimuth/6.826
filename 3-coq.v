Global Set Default Goal Selector "!".

Require Import Arith.
Require Import Lia.

Record nbpair := mkpair {
  first : nat;
  second : bool;
}.

Search negb.

Theorem t2 :
  forall x b,
    mkpair (x+x-x) b = mkpair x (negb (negb b)).
Proof.
  intros.
  f_equal.
  (*- rewrite Nat.add_sub. reflexivity.*)
  (*- eauto. (* fully solves goal using "hints" or does nothing. not the same as "auto" due to
   search differences. *)*)
  - lia. (* can do anything: labs are practice where it doesn't apply. *)
  - rewrite Bool.negb_involutive. reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
  induction n.
  - simpl.
    eauto.
  - intros.
    simpl.
    rewrite IHn.
    rewrite plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
    n * (m * p) = (n * m) * p.
Proof.
  induction n.
  - intros.
    simpl.
    reflexivity.
  - intros.
    simpl.
