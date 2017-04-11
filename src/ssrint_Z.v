(* Generic part *)

From Transfer Require Import Transfer.
From Coq Require Import Program.Basics.
From mathcomp Require Import ssrbool.

Instance prop_bool : Related (reflect ##> iff) id is_true.
Proof.
  intros ? ? H.
  now inversion H.
Qed.

(* Part specifically dedicated to ssrint. *)
(* Based on the work by Nicolas Magaud. *)

From Coq Require Import ZArith.
From mathcomp Require Import ssrnum ssrint ssrnat ssreflect ssralg.

Set Bullet Behavior "Strict Subproofs".

Open Scope Z_scope.

Definition Z_of_int (x : int) :=
  match x with
  | Posz t => Z.of_nat t
  | Negz t => (Zminus (Z.opp (Z.of_nat t)) 1)
  end.

Definition int_of_Z (x : Z) : int :=
  match x with
  | Z0 => Posz 0%nat
  | Zpos p => Posz (nat_of_pos p)
  | Zneg p => Negz( (nat_of_pos p).-1 )
  end.

Definition R (a : Z) (b : int) := a = Z_of_int b.

Instance Biunique_R_1 : Related (R ##> R ##> impl) eq eq.
Proof.
  unfold R, Z_of_int.
  intros ? [ n | n ] -> ? [ n' | n' ] -> ?.
  - now rewrite <- (Nat2Z.inj n n').
  - omega.
  - omega.
  - apply f_equal.
    omega.
Qed.

Lemma Biunique_R_2 : Related (flip R ##> flip R ##> impl) eq eq.
Proof.
  now intros ? ? -> ? ? -> H; inversion H.
Qed.

Instance Biunique_R : Related (R ##> R ##> iff) eq eq.
Proof.
  split.
  - now apply Biunique_R_1.
  - now apply Biunique_R_2.
Qed.

Lemma of_nat_nat_of_pos : forall p : positive, Z.pos p = Z.of_nat (nat_of_pos p).
Proof.
  induction p; simpl.
  - rewrite Pos2Z.inj_xI.
    rewrite NatTrec.trecE.
    rewrite <- addnn.
    rewrite Zpos_P_of_succ_nat.
    rewrite Nat2Z.inj_add.
    rewrite <- IHp.
    ring.
  - rewrite Pos2Z.inj_xO.
    rewrite NatTrec.trecE.
    rewrite <- addnn.
    rewrite Nat2Z.inj_add.
    rewrite <- IHp.
    ring.
  - reflexivity.
Qed.

Lemma nat_of_pos_lt_0 : forall p, (0 < nat_of_pos p)%coq_nat.
Proof.
  induction p; simpl.
  - rewrite NatTrec.trecE.
    apply Nat.lt_0_succ.
  - rewrite NatTrec.trecE.
    rewrite <- addnn.
    replace 0%nat with (0+0)%nat by ring.
    apply plus_lt_compat; apply IHp.
  - apply Nat.lt_0_1.
Qed.

Lemma of_nat_nat_of_pos_1 : forall p, (Z.of_nat ((nat_of_pos p).-1) = (Z.of_nat (nat_of_pos p))-1).
Proof.
  induction p; simpl nat_of_pos.
  - rewrite NatTrec.trecE.
    rewrite <- addnn.
    rewrite Nat2Z.inj_succ.
    rewrite Nat2Z.inj_add.
    rewrite <- of_nat_nat_of_pos.
    ring.
  - rewrite NatTrec.trecE.
    rewrite <- addnn.
    rewrite Nat2Z.inj_pred.
    rewrite Nat2Z.inj_add.
    rewrite <- of_nat_nat_of_pos.
    unfold Z.pred; ring.
    replace 0%nat with (0+0)%nat by ring.
    apply plus_lt_compat; apply nat_of_pos_lt_0.
  - reflexivity.
Qed.

Instance bitotal_R_1 : Related ((R ##> impl) ##> impl) (@all Z) (@all int).
Proof.
  intros ? ? H ? ?.
  now eapply H.
Qed.

Instance bitotal_R : Related ((R ##> iff) ##> iff) (@all Z) (@all int).
Proof.
  unfold R,all, "##>"; repeat red.
  intros e e' o.
  split.
  - intros.
    now apply -> o.
  - intros.
    apply <- o.
    apply (H (int_of_Z x)).
    unfold Z_of_int, int_of_Z; destruct x.
    + reflexivity.
    + apply of_nat_nat_of_pos.
    + rewrite of_nat_nat_of_pos_1.
      rewrite <- of_nat_nat_of_pos.
      ring_simplify.
      reflexivity.
Qed.

Lemma lt_transfer : Related (R ##> R ##> iff) Z.lt Num.Def.ltr.
Proof.
  unfold R, Z_of_int.
  intros ? [] -> ? [] ->; split; intros H.
  - rewrite <- Nat2Z.inj_lt in H.
    now apply /leP.
  - rewrite <- Nat2Z.inj_lt.
    now apply /leP.
  - omega.
  - easy.
  - easy.
  - omega.
  - apply /leP; omega.
  - apply Z.lt_sub_lt_add.
    rewrite Z.add_comm.
    apply Z.add_lt_mono_l.
    rewrite <- Z.opp_lt_mono.
    rewrite <- Nat2Z.inj_lt.
    now apply /ltP.
Qed.

Instance lt_transfer_rule : Related (R ##> R ##> reflect) Z.lt Num.Def.ltr.
Proof.
  intros x x' Hx y y' Hy.
  apply introP; intro H1;
  specialize (lt_transfer x x' Hx y y' Hy) as H2.
  - now apply H2.
  - revert H1. move => /negPf H3 H4. apply H2 in H4. now rewrite H4 in H3.
Qed.

Lemma N_ok : forall n n0:nat, (n0 < n)%N = false -> (n <= n0)%N.
Proof.
  intros.
  rewrite ltnNge in H.
  now apply Bool.negb_false_iff in H.
Qed.

Lemma N_ok3 : forall n n0:nat, (n <= n0)%N = true -> (n <= n0)%coq_nat.
Proof.
  repeat red.
  intros.
  generalize (@leP n n0 H); intros F.
  apply F.
Qed.

Instance add_transfer : Related (R ##> R ##> R) Z.add intZmod.addz.
Proof.
  unfold R, Z_of_int.
  intros ? [ x1' | x1' ] -> ? [ x2' | x2' ] ->; simpl.
  - now rewrite inj_plus.
  - destruct (x2' < x1')%N eqn:?.
    + rewrite -> Nat2Z.inj_sub, Nat2Z.inj_succ by now apply lt_le_S, N_ok3.
      ring.
    + rewrite -> Nat2Z.inj_sub by now apply N_ok3, N_ok.
      ring.
  - destruct (x1' < x2')%N eqn:?.
    + rewrite -> Nat2Z.inj_sub, Nat2Z.inj_succ by now apply lt_le_S, N_ok3.
      ring.
    + rewrite -> Nat2Z.inj_sub by now apply N_ok3, N_ok.
      ring.
  - rewrite <- Pos2Z.opp_pos.
    rewrite Z.add_assoc.
    replace (- Z.of_nat x1' - 1 + - Z.of_nat x2' + - (1))
    with (- (Z.of_nat x1' + Z.of_nat x2' + Z.of_nat 2))
      by ring.
    rewrite <- Nat2Z.inj_add, Pos2Z.inj_add, Zpos_P_of_succ_nat.
    ring_simplify; reflexivity.
Qed.

Typeclasses Opaque Num.Def.ltr intZmod.addz.
(* This is the kind of hint which justify not using the default typeclass_instances
   database. *)
