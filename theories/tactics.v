(* File contributed by Nicolas Magaud *)
(* Cf. "Transferring Arithmetic Decision Procedures (on Z) to Alternative Representations" *)
(* presented at CoqPL 2017 *)

Require Import Transfer iso_ssrint.
From Coq Require Import ZArith Psatz.

Tactic Notation "tomega" := transfer; simpl (f _); intros; omega.
Tactic Notation "tring" := transfer; simpl (f _); intros; ring.
Tactic Notation "tlia" := transfer; simpl (f _); intros; lia.
Tactic Notation "tpsatz" := transfer; simpl (f _); intros; psatz Z.

Ltac wrap := match goal with | [|- forall  x:_, _] => intro x ; wrap; revert x| _ => generalize I end.
Ltac wtransfer := wrap; transfer; simpl (f _).
