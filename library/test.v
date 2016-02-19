Require Import Utf8.
Require Import PeanoNat.
Require Import NArithTransfer.

Instance adhoc
  (A B : Type)
  (R : A -> B -> Prop)
  (inst : Related (R ##> R ##> iff) eq eq) :
  Related (((R ##> iff) ##> iff) ##> iff) (@all (A -> Prop)) (@all (B -> Prop)).
Proof.
  assert (prf := prf); unfold respectful_arrow in prf.
  split; apply full_tot_decl; split.
  + intros P'.
    exists (fun x => forall x', R x x' -> P' x').
    intros x x' relx; split; auto; intros HP' y' relxy.
    destruct (prf x x' relx x y' relxy) as [prf' _].
    now rewrite <- prf'.
  + intros P.
    exists (fun x' => forall x, R x x' -> P x).
    intros x x' relx; split; auto; intros HP y relyx.
    destruct (prf x x' relx y x' relyx) as [_ prf'].
    now rewrite <- prf'.
Qed.

(*  Alternative proof with alternative predicate:
    exists (fun x => exists x', R x x' /\ P' x').
    intros x x' relx; split; [ |firstorder ].
    intros (y' & relxy & Hy).
    destruct (prf x x' relx x y' relxy) as [prf' _].
    now rewrite prf'. *)
(*  Alternative complete proof with more symmetry
Proof.
  assert (prf := prf); unfold respectful_arrow in prf.
  assert (prf' : (flip R ##> flip R ##> iff) eq eq). {
    lazy beta delta; firstorder.
    rewrite prf; eauto.
    rewrite <- prf; eauto.
  }
  split; apply surj_tot_decl; split.
  + intros P'.
    exists (fun x => forall x', R x x' -> P' x').
    intros x x' relx; split; auto; intros HP' y' relxy.
    edestruct prf as [prf1 _].
    eexact relx.
    eexact relxy.
    now rewrite <- prf1.
  + intros P'.
    exists (fun x => forall x', flip R x x' -> P' x').
    intros x x' relx; split; auto; intros HP' y' relxy.
    edestruct prf' as [prf1 _].
    eexact relx.
    eexact relxy.
    now rewrite <- prf1.
Qed.
*)

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  exact (modulo nat_ind).
Qed.

Theorem ex2 : forall n : nat, n = n.
  Fail rewrite <- Nat.pred_succ. (* bizarre *)
  Fail rewrite <- Nat.add_0_l. (* idem *)