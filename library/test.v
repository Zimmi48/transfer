Require Import Utf8.
Require Import PeanoNat.
Require Import NArithTransfer.

Instance adhoc : Related (((natN ##> iff) ##> impl) ##> impl) (@all (nat → Prop)) (@all (N → Prop)).
Proof.
  related_basics.
  intros PP PP' bigH PPuniversal P'.
  set (P := fun n => P' (N.of_nat n)).
  apply (bigH P P'); [| now apply PPuniversal ].
  intros n n' rel.
  unfold P.
  unfold natN in rel.
  now rewrite rel.
Qed.

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  Typeclasses eauto := debug.
  Fail exact (modulo nat_ind).

Theorem ex1 : forall n : N, n = n.
  Typeclasses eauto := debug.
  Fail apply (modulo nat_ind).
Abort.

Theorem ex2 : forall n : nat, n = n.
  Fail rewrite <- Nat.pred_succ. (* bizarre *)
  Fail rewrite <- Nat.add_0_l. (* idem *)