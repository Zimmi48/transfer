(* Examples of transfer from nat to N *)
(* To evaluate this file,
 * run coqc on Transfer.v and NArithTransfer.v and run coq with:
 * $coqide -I . NArithTests.v
 *)

Require Import PeanoNat.
Require Import NArithTransfer.

(** ** Basic specifications : pred add sub mul *)

Lemma pred_succ : forall n, N.pred (N.succ n) = n.
Proof.
  Typeclasses eauto := debug.
  Fail apply modulo.
  exact (modulo Nat.pred_succ).
Qed.

Lemma pred_0 : N.pred 0 = 0%N.
Proof.
  apply modulo.
  reflexivity.
  (*exact (modulo Nat.pred_0).*)
Qed.

Lemma one_succ : 1%N = N.succ 0%N.
Proof.
  apply modulo.
  reflexivity.
  (*exact (modulo Nat.one_succ).*)
Qed.

Lemma two_succ : 2%N = N.succ 1%N.
Proof.
  apply modulo.
  reflexivity.
  (*exact (modulo Nat.two_succ).*)
Qed.

Lemma add_0_l : forall n, N.add 0 n = n.
Proof.
  Fail apply modulo.
  exact (modulo Nat.add_0_l).
Qed.

Lemma add_succ_l :
  forall n m, N.add (N.succ n) m = N.succ (N.add n m).
Proof.
  Fail apply modulo.
  exact (modulo Nat.add_succ_l).
Qed.

Lemma suc_0_r : forall n, N.sub n 0 = n.
Proof.
  Fail apply modulo.
  exact (modulo Nat.sub_0_r).
Qed.

Lemma sub_succ_r :
  forall n m, N.sub n (N.succ m) = N.pred (N.sub n m).
Proof.
  Fail apply modulo.
  exact (modulo Nat.sub_succ_r).
Qed.

Lemma mul_0_l : forall n, N.mul 0%N n = 0%N.
Proof.
  Fail apply modulo.
  exact (modulo Nat.mul_0_l).
Qed.

Lemma mul_succ_l :
  forall n m, N.mul (N.succ n) m = N.add (N.mul n m) m.
Proof.
  Fail apply modulo.
  exact (modulo Nat.mul_succ_l).
Qed.

(* The following cannot be transfered for now because the required
   transfer rules are missing. *)
(*
Lemma lt_succ_r : forall n m : N, n < S m <-> n <= m.
Proof.
  exact (modulo Nat.lt_succ_r).
Qed.

(** ** Boolean comparisons *)

Lemma eqb_eq : forall n m : N, eqb n m = true <-> n = m.
Proof.
  exact (modulo Nat.eqb_eq).
Qed.

Lemma leb_le : forall n m : N, (n <=? m) = true <-> n <= m.
Proof.
  exact (modulo Nat.leb_le).
Qed.

Lemma ltb_lt : forall n m : N, (n <? m) = true <-> n < m.
Proof.
  exact (modulo Nat.ltb_lt).
Qed.

(** ** Decidability of equality over [nat]. *)

Lemma eq_dec : forall n m : N, {n = m} + {n <> m}.
Proof.
  exact (modulo Nat.eq_dec).
Qed.
*)

(** ** Ternary comparison *)

Lemma compare_eq_iff : forall n m, N.compare n m = Eq <-> n = m.
Proof.
  Fail apply modulo.
  exact (modulo Nat.compare_eq_iff).
Qed.

(*
Lemma compare_lt_iff : forall n m, N.compare n m = Lt <-> n < m.
Proof.
  exact (modulo Nat.compare_lt_iff).
Qed.

Lemma compare_le_iff : forall n m, N.compare n m <> Gt <-> n <= m.
Proof.
  exact (modulo Nat.compare_le_iff).
Qed.

Lemma compare_antisym : forall n m, N.compare n m = CompOpp (n ?= m).
Proof.
  exact (modulo Nat.compare_antisym).
Qed.
*)

Lemma compare_succ :
  forall n m, N.compare (N.succ n) (N.succ m) = N.compare n m.
Proof.
  Fail apply modulo.
  exact (modulo Nat.compare_succ).
Qed.
