Require Import Utf8.
Require Import PeanoNat.
Require Import NArithTransfer.

Instance total_predicate
  (A B : Type)
  (R : A -> B -> Prop)
  (inst : Related (R ##> R ##> iff) eq eq) :
  Related (((R ##> iff) ##> iff) ##> iff) (@all (A -> Prop)) (@all (B -> Prop)).
Proof.
  destruct (full_uniq_decl_recip _ _ _ prf) as [ Hfun Hinj ].
  split; apply full_tot_decl; split.
  + intros P'.
(*  exists (fun x => exists x', R x x' /\ P' x'). *)
    exists (fun x => forall x', R x x' -> P' x').
    intros; split; firstorder.
    erewrite Hfun; eauto.
  + intros P.
    exists (fun x' => exists x, R x x' /\ P x).
(*  exists (fun x' => forall x, R x x' -> P x). *)
    intros; split; firstorder.
    erewrite Hinj; eauto.
Qed.

Lemma total_predicate_recip :
  forall (A B : Type) (R : A -> B -> Prop),
  (((R ##> iff) ##> iff) ##> iff) (@all (A -> Prop)) (@all (B -> Prop)) ->
  ((R ##> iff) ##> (R ##> iff) ##> iff) eq eq ->
  (R ##> R ##> iff) eq eq.
Proof.
Abort.

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  transfer.
  exact nat_ind.
(*   exactm nat_ind. *)
Qed.

Theorem ex2 : forall n : nat, n = n.
Proof.
  Fail rewrite <- Nat.pred_succ. (* bizarre *)
  Fail rewrite <- Nat.add_0_l. (* idem *)
  apply nat_ind.
Abort.

Theorem ex3: forall n : N, n = n.
Proof.
  apply N_nat_ind.


