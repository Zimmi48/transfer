(* File contributed by Nicolas Magaud *)
(* Cf. "Transferring Arithmetic Decision Procedures (on Z) to Alternative Representations" *)
(* presented at CoqPL 2017 *)

Require Import Transfer tactics iso_ssrint.
From Coq Require Import ZArith.
From mathcomp Require Import ssrnum ssrint ssrbool ssralg.

Open Scope ring_scope.

Notation "x + y" := (intZmod.addz x y) : ring_scope.
Notation "x < y" := (ltr' x y) : ring_scope.

(* this notation "<" already exists in ssrnum.v and the notation "+" exists in ssralg.v *)

Lemma foo1 : forall x y:int, x + y = y + x.
Proof.
  intros x y; generalize I; revert x y.
  tomega.
Qed.

Lemma foo2 :forall x1 y1 z1 : int, x1 = y1 -> x1 + z1 = y1 + z1.
Proof.
  tomega.
Qed.

(*Lemma foo3' : forall (x y : int), (x < y) -> (y < x).
Proof.
  Print arrow. (* in Type *)
  Print impl. (* in Prop *)
  intros x y H.
  Restart.
  transfer.
Abort.
*)

(*  intros x y H.
  eapply lt_transfer2. (* apply says "unable to unify..." *)
  apply rel1.
  apply rel1.
  eapply lt_transfer2 in H; [idtac | apply rel1 | apply rel1].*)

Lemma foo3 : forall (x y z t : int), (x < y) -> (z < t)  -> (x+z < y+t).
Proof.
  tomega.
Qed.
