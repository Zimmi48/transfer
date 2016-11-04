(* Transfer between N and nat *)
(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Export Transfer.Transfer Coq.NArith.BinNatDef.
Require Import Coq.NArith.Nnat.

Definition natN x x' := N.of_nat x = x'.

Instance natN_nb : forall n : nat, Related natN n (N.of_nat n) | 10.
Proof. reflexivity. Defined.

Instance natN_nb' : forall n : N, Related natN (N.to_nat n) n | 10.
Proof. apply N2Nat.id. Defined.

(* Totality of natN *)

Instance natN_bitotal :
  Related ((natN ##> iffT) ##> iffT) forall_def forall_def.
Proof.
  related_basics.
  unfold natN.
  intros f1 f2 Hf; split; intros H x.
  + apply (Hf (N.to_nat x)); trivial.
    apply N2Nat.id.
  + apply Hf with (e' := N.of_nat x); trivial.
Defined.

Module N2Nat_transfer.

(* Preliminaries *)

Lemma natN_bis x x' : natN x x' -> N.to_nat x' = x.
Proof.
  unfold natN.
  intros H.
  rewrite <- H.
  apply Nat2N.id.
Defined.

Lemma natN_bis_recip x x' : N.to_nat x' = x -> natN x x'.
Proof.
  unfold natN.
  intros H.
  rewrite <- H.
  apply N2Nat.id.
Defined.

Ltac unfold_natN_bis :=
  let n' := fresh "n" in
  let n := fresh "n" in
  let Hn := fresh "Hn" in
  intros n n' Hn;
  apply natN_bis in Hn;
  rewrite <- Hn;
  clear Hn n.

Import N2Nat.

Ltac solve thm :=
  related_basics;
  repeat unfold_natN_bis;
  try (apply natN_bis_recip);
  (apply thm || symmetry ; apply thm).

(* This symmetry is required for some theorem which
   we translate with eq when we should really have used
   flip eq *)

(* Rewrite all theorems from N2Nat *)

Instance inj : Related (natN ##> natN ##> arrow) eq eq.
Proof.
  solve inj.
Defined.

Instance inj_iff : Related (natN ##> natN ##> iff) eq eq.
Proof.
  solve inj_iff.
Defined.

Instance inj_iffT : Related (natN ##> natN ##> iffT) eq eq.
Proof.
  intros ? ? reln ? ? relm.
  split;
  unfold natN in *.
  - rewrite <- reln.
    intros -> .
    assumption.
  - rewrite <- relm.
    intros -> .
    now apply Nat2N.inj.
Defined.

(* inj_double, inj_succ_double *)

Instance inj_succ : Related (natN ##> natN) S N.succ.
Proof.
  solve inj_succ.
Defined.

Instance inj_add : Related (natN ##> natN ##> natN) Nat.add N.add.
Proof.
  solve inj_add.
Defined.

Instance inj_mul : Related (natN ##> natN ##> natN) Nat.mul N.mul.
Proof.
  solve inj_mul.
Defined.

Instance inj_sub : Related (natN ##> natN ##> natN) Nat.sub N.sub.
Proof.
  solve inj_sub.
Defined.

Instance inj_pred : Related (natN ##> natN) Nat.pred N.pred.
Proof.
  solve inj_pred.
Defined.

Instance inj_div2 : Related (natN ##> natN) Nat.div2 N.div2.
Proof.
  solve inj_div2.
Defined.

Instance inj_compare :
  Related (natN ##> natN ##> eq) Nat.compare N.compare.
Proof.
  solve inj_compare.
Defined.

Instance inj_max : Related (natN ##> natN ##> natN) Nat.max N.max.
Proof.
  solve inj_max.
Defined.

Instance inj_min : Related (natN ##> natN ##> natN) Nat.min N.min.
Proof.
  solve inj_min.
Defined.

Instance inj_iter :
  forall {A} (f : A -> A) (x : A),
  Related (natN ##> eq)
    (fun n => Nat.iter n f x) (fun n => N.iter n f x).
Proof.
  solve inj_iter.
Defined.

End N2Nat_transfer.

Module Nat2N_transfer.

Import Nat2N.

(* Preliminaries *)

Ltac unfold_natN :=
  let n := fresh "n" in
  let n' := fresh "n" in
  let Hn := fresh "Hn" in
  intros n n' Hn;
  unfold natN in Hn;
  rewrite <- Hn;
  clear Hn n'.

Ltac solve thm :=
  related_basics;
  repeat unfold_natN;
  try (rewrite natN);
  apply thm.

Instance inj : Related (natN ##> natN ##> flip impl) eq eq.
Proof.
  solve inj.
Defined.

(* The rest would mean proving all the same theorems again,
   so we won't do it although that can be done. *)

(* Etc *)

End Nat2N_transfer.

