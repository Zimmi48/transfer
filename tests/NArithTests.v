(* Examples of transfer from nat to N *)

From Coq Require Import PeanoNat NArith.
From Transfer Require Import Transfer Respectful NArithTransfer.

(** ** Basic specifications : pred add sub mul *)

Lemma pred_succ : forall n, N.pred (N.succ n) = n.
Proof.
  intro.
  transfer.
  apply Nat.pred_succ.
Qed.

Lemma pred_0 : N.pred 0 = 0%N.
Proof.
  transfer.
  reflexivity.
Qed.

Lemma one_succ : 1%N = N.succ 0%N.
Proof.
  transfer.
  reflexivity.
Qed.

Lemma two_succ : 2%N = N.succ 1%N.
Proof.
  transfer.
  reflexivity.
Qed.

Lemma add_0_l : forall n, N.add 0 n = n.
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

Lemma add_succ_l :
  forall n m, N.add (N.succ n) m = N.succ (N.add n m).
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

Lemma suc_0_r : forall n, N.sub n 0 = n.
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

Lemma sub_succ_r :
  forall n m, N.sub n (N.succ m) = N.pred (N.sub n m).
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

Lemma mul_0_l : forall n, N.mul 0%N n = 0%N.
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

Lemma mul_succ_l :
  forall n m, N.mul (N.succ n) m = N.add (N.mul n m) m.
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

(** ** Ternary comparison *)

Lemma compare_eq_iff : forall n m, N.compare n m = Eq <-> n = m.
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

Lemma compare_succ :
  forall n m, N.compare (N.succ n) (N.succ m) = N.compare n m.
Proof.
  Fail transfer.
  (* FIXME *)
Abort.

(** ** A theorem of recursion. *)

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  transfer.
  cbn.
  exact nat_ind.
Qed.
