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
  exact (modulo Nat.pred_succ).
Qed.

Lemma pred_0 : N.pred 0 = 0%N.
Proof.
  exact (modulo Nat.pred_0).
Qed.

Lemma one_succ : 1%N = N.succ 0%N.
Proof.
  exact (modulo Nat.one_succ).
Qed.

Lemma two_succ : 2%N = N.succ 1%N.
Proof.
  exact (modulo Nat.two_succ).
Qed.

Lemma add_0_l : forall n, N.add 0 n = n.
Proof.
  exact (modulo Nat.add_0_l).
Qed.

Lemma add_succ_l :
  forall n m, N.add (N.succ n) m = N.succ (N.add n m).
Proof.
  exact (modulo Nat.add_succ_l).
Qed.

Lemma suc_0_r : forall n, N.sub n 0 = n.
Proof.
  exact (modulo Nat.sub_0_r).
Qed.

Lemma sub_succ_r :
  forall n m, N.sub n (N.succ m) = N.pred (N.sub n m).
Proof.
  exact (modulo Nat.sub_succ_r).
Qed.

Lemma mul_0_l : forall n, N.mul 0%N n = 0%N.
Proof.
  exact (modulo Nat.mul_0_l).
Qed.

Lemma mul_succ_l :
  forall n m, N.mul (N.succ n) m = N.add (N.mul n m) m.
Proof.
  exact (modulo Nat.mul_succ_l).
Qed.

(* The following cannot be transfered for now because the required
   transfer rules are missing. *)
(*
Lemma lt_succ_r n m : n < S m <-> n <= m.
Proof.
  exact (modulo Nat.lt_succ_r).
Qed.

(** ** Boolean comparisons *)

Lemma eqb_eq n m : eqb n m = true <-> n = m.
Proof.
  exact (modulo Nat.eqb_eq).
Qed.

Lemma leb_le n m : (n <=? m) = true <-> n <= m.
Proof.
  exact (modulo Nat.leb_le).
Qed.

Lemma ltb_lt n m : (n <? m) = true <-> n < m.
Proof.
  exact (modulo Nat.ltb_lt).
Qed.

(** ** Decidability of equality over [nat]. *)

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  exact (modulo Nat.eq_dec).
Qed.
*)

(** ** Ternary comparison *)

(* Proof containing iff will require special care. *)
(*
Lemma compare_eq_iff : forall n m, N.compare n m = Eq <-> n = m.
Proof.
Typeclasses eauto := debug.
  Fail exact (modulo Nat.compare_eq_iff).
Abort.

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
  exact (modulo Nat.compare_succ).
Qed.
