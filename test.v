Require Import Coq.Arith.PeanoNat.
Require Import Transfer.NArithTransfer.

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  Typeclasses eauto := debug.
  enough (H : Related arrow
                (forall P : nat -> Prop, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n)
                (forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n))
    by (apply H; exact nat_ind).
  apply forall_rule.
  eapply app_rule. (* (app_rule _ _ _ _ ((natN ##> iff) ##> iffT)). *)
  eapply subrel_rule; [ apply sub_respectful_right; exact sub_iffT_arrow |].
  apply total_predicate_prop.
  exact N2Nat_transfer.inj_iffT.
  apply lambda_rule; intros P P' relP.
  apply arrow_rule.
  eapply app_rule; [ eapply app_rule; [ exact arrow_transfer_rule |] |].
  eapply app_rule.
  refine _.
  eapply app_rule.
  
Qed.

(*
Set Printing Universes.
Print N_nat_ind.
*)

Theorem ex2 : forall n : nat, n = n.
Proof.
  Fail rewrite <- Nat.pred_succ. (* bizarre *)
  Fail rewrite <- Nat.add_0_l. (* idem *)
  apply nat_ind.
Abort.

Theorem ex3: forall n : N, n = n.
Proof.
  applym nat_ind.
  simpl.
(* Is equivalent to:
  apply N_nat_ind. *)


