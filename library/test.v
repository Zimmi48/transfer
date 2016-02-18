Require Import Utf8.
Require Import PeanoNat.
Require Import NArithTransfer.

Instance natN_iff :
  Related ((natN ##> iff) ##> iff) (@all nat) (@all N).
Proof.
  split; apply surj_tot_decl; split.
  + apply surj_decl; apply natN_surjective.
  + apply tot_decl; apply natN_total.
Qed.

Instance adhoc
  (A B : Type)
  (R : A -> B -> Prop)
  (inst : Related (R ##> R ##> iff) eq eq) :
  Related (((R ##> iff) ##> iff) ##> iff) (@all (A -> Prop)) (@all (B -> Prop)).
Proof.
  related_basics.
  assert (prf := prf); unfold respectful_arrow in prf.
  intros PP PP' bigH; split.
  + intros PPuniversal P'.
    apply (bigH (fun x => forall x', R x x' -> P' x') P'); [| now apply PPuniversal ].
    intros n n' rel; split; auto; intros HP' x' rel2.
    destruct (prf n n' rel n x' rel2) as [prf' _].
    now rewrite <- prf'.
  + intros PP'universal P.
    apply (bigH P (fun x' => forall x, R x x' -> P x)); [| now apply PP'universal ].
    intros n n' rel; split; auto; intros HP x rel2.
    destruct (prf n n' rel x n' rel2) as [_ prf'].
    now rewrite <- prf'.
Qed.

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  Typeclasses eauto := debug.
  exact (modulo nat_ind).
Qed.

Theorem ex2 : forall n : nat, n = n.
  Fail rewrite <- Nat.pred_succ. (* bizarre *)
  Fail rewrite <- Nat.add_0_l. (* idem *)