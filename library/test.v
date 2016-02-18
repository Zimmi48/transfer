Require Import Utf8.
Require Import PeanoNat.
Require Import NArithTransfer.

Instance adhoc : Related (((natN ##> iff) ##> iff) ##> iff) (@all (nat → Prop)) (@all (N → Prop)).
Proof.
  related_basics.
  intros PP PP' bigH.
  split.
  + intros PPuniversal P'.
    set (P := fun n => P' (N.of_nat n)).
    apply (bigH P P'); [| now apply PPuniversal ].
    intros n n' rel.
    unfold P.
    unfold natN in rel.
    now rewrite rel.
  + intros PP'universal P.
    set (P' := fun n => P (N.to_nat n)).
    apply (bigH P P'); [| now apply PP'universal ].
    intros n n' rel.
    unfold P'.
    rewrite N2Nat_transfer.natN_bis in rel.
    now rewrite <- rel.
Qed.

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  Typeclasses eauto := debug.
  exact (modulo nat_ind).
Qed.

Theorem ex2 : forall n : nat, n = n.
  Fail rewrite <- Nat.pred_succ. (* bizarre *)
  Fail rewrite <- Nat.add_0_l. (* idem *)