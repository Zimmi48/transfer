(* File contributed by Nicolas Magaud *)
(* Cf. "Transferring Arithmetic Decision Procedures (on Z) to Alternative Representations" *)
(* presented at CoqPL 2017 *)

From mathcomp Require Import ssrint ssrnum ssrbool.
From Coq Require Import ZArith Lia.
Require Import Transfer tactics iso_ssrint.

Notation "x + y" := (intZmod.addz x y).
Notation "x - y" := (x + intZmod.oppz y).
Notation "x * y" := (intRing.mulz x y).

Definition le3r' (x y z:int) : Prop := (ler' x y) /\ (ler' y z).

Instance le3_transfer : Related (R ##> R ##> R##> iff) (fun x y z => x <= y /\ y <= z) le3r'.
Proof.
repeat red; intros; split; unfold le3r'; intros.
inversion H2.
split.
eapply le_transfer; eassumption.
eapply le_transfer; eassumption.
inversion H2.
split.
eapply le_transfer; eassumption.
eapply le_transfer; eassumption.
Qed.

Notation "x <= y" := (ler' x y).
Notation " x < y" := (ltr' x y).
Notation "x <= y <= z" := (le3r' x y z).
Notation "x >= y" := (ger' x y).
Notation " x > y" := (gtr' x y).

Open Scope int_scope.
Notation "0" := 0%:Z.
Notation "1" := 1%:Z.
Notation "2" := 2%:Z.
Notation "27" := 27%:Z.
Notation "11" := 11%:Z.
Notation "13" := 13%:Z.
Notation "45" := 45%:Z.
Notation "- 10" := (intZmod.oppz 10%:Z).
Notation "7" := 7%:Z.
Notation "9" := 9%:Z.
Notation "4" := 4%:Z.

Close Scope int_scope.

Lemma two_x_eq_1 : forall x, 2 * x = 1 -> False.
Proof.
  tlia.
Qed.

Lemma two_x_y_eq_1 : forall x y, 2 * x + 2 * y = 1 -> False.
Proof.
  tlia.
Qed.

Lemma two_x_y_z_eq_1 : forall x y z, 2 * x + 2 * y + 2 * z= 1 -> False.
Proof.
  tlia.
Qed.

Lemma omega_nightmare : forall x y:int, 27 <= 11 * x + 13 * y <= 45 -> -10 <= 7 * x - 9 * y <= 4 -> False.
tlia.
Qed.

Lemma compact_proof : forall z:int,
 (z < 0) ->
 (z >= 0) ->
  (0 >= z \/ 0 < z) -> False.
Proof.
 tlia.
Qed.
