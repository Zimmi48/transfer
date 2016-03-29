(* Examples of transfer from nat to N *)

Axiom mix : forall A : Type, A -> A -> A.
Tactic Notation "give_2_proofs" := apply mix.

Tactic Notation "give_3_proofs" := apply mix; [apply mix|].

Require Import PeanoNat.
Require Import NArithTransfer.

(** ** Basic specifications : pred add sub mul *)

Lemma pred_succ : forall n, N.pred (N.succ n) = n.
Proof.
  enough (H: impl (forall n : nat, Nat.pred (S n) = n) (forall n : N, N.pred (N.succ n) = n))
    by (apply H; exact Nat.pred_succ).
  eapply forall_rule.
  eapply app_rule.
  Check lambda_rule.
  eapply lambda_rule.
  intro; intro; intro.
  eapply forall_rule.
  eapply app_rule;
    [ eapply lambda_rule;
      intro; intro; intro;
      eapply forall_rule;
      clear H x x'; rename H0 into H; rename x0 into x; rename x'0 into x' |].
  (* infinite loop *)
  exactm Nat.pred_succ.
Qed.

Lemma pred_0 : N.pred 0 = 0%N.
Proof.
  give_3_proofs.
  - transfer.
    reflexivity.
  - exactm Nat.pred_0.
  - applym Nat.pred_0.
Qed.

Lemma one_succ : 1%N = N.succ 0%N.
Proof.
  give_3_proofs.
  - transfer.
    reflexivity.
  - exactm Nat.one_succ.
  - applym Nat.one_succ.
Qed.

Lemma two_succ : 2%N = N.succ 1%N.
Proof.
  give_3_proofs.
  - transfer.
    reflexivity.
  - exactm Nat.two_succ.
  - applym Nat.two_succ.
Qed.

Lemma add_0_l : forall n, N.add 0 n = n.
Proof.
  exactm Nat.add_0_l.
(*  applym Nat.add_0_l. *)
(*  Does not work anymore because of current limitation to apply modulo. *)
Qed.

Lemma add_succ_l :
  forall n m, N.add (N.succ n) m = N.succ (N.add n m).
Proof.
  exactm Nat.add_succ_l.
Qed.

Lemma suc_0_r : forall n, N.sub n 0 = n.
Proof.
  exactm Nat.sub_0_r.
Qed.

Lemma sub_succ_r :
  forall n m, N.sub n (N.succ m) = N.pred (N.sub n m).
Proof.
  exactm Nat.sub_succ_r.
Qed.

Lemma mul_0_l : forall n, N.mul 0%N n = 0%N.
Proof.
  exactm Nat.mul_0_l.
Qed.

Lemma mul_succ_l :
  forall n m, N.mul (N.succ n) m = N.add (N.mul n m) m.
Proof.
  exactm Nat.mul_succ_l.
Qed.

(* The following cannot be transfered for now because the required
   transfer rules are missing. *)
(*
Lemma lt_succ_r : forall n m : N, n < S m <-> n <= m.
Proof.
  exactm Nat.lt_succ_r.
Qed.

(** ** Boolean comparisons *)

Lemma eqb_eq : forall n m : N, eqb n m = true <-> n = m.
Proof.
  exactm Nat.eqb_eq.
Qed.

Lemma leb_le : forall n m : N, (n <=? m) = true <-> n <= m.
Proof.
  exactm Nat.leb_le.
Qed.

Lemma ltb_lt : forall n m : N, (n <? m) = true <-> n < m.
Proof.
  exactm Nat.ltb_lt.
Qed.

(** ** Decidability of equality over [nat]. *)

Lemma eq_dec : forall n m : N, {n = m} + {n <> m}.
Proof.
  exactm Nat.eq_dec.
Qed.
*)

(** ** Ternary comparison *)

Lemma compare_eq_iff : forall n m, N.compare n m = Eq <-> n = m.
Proof.
  exactm Nat.compare_eq_iff.
Qed.

(*
Lemma compare_lt_iff : forall n m, N.compare n m = Lt <-> n < m.
Proof.
  exactm Nat.compare_lt_iff.
Qed.

Lemma compare_le_iff : forall n m, N.compare n m <> Gt <-> n <= m.
Proof.
  exactm Nat.compare_le_iff.
Qed.

Lemma compare_antisym : forall n m, N.compare n m = CompOpp (n ?= m).
Proof.
  exactm Nat.compare_antisym.
Qed.
*)

Lemma compare_succ :
  forall n m, N.compare (N.succ n) (N.succ m) = N.compare n m.
Proof.
  exactm Nat.compare_succ.
Qed.

(** ** A theorem of recursion. *)

Theorem N_nat_rect : forall P : N -> Type, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  give_3_proofs.
  - transfer.
    cbn.
    exact nat_rect.
  - exactm nat_rect.
  - applym nat_rect.
Qed.
