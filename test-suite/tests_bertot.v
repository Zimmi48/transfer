(* File contributed by Nicolas Magaud *)
(* Cf. "Transferring Arithmetic Decision Procedures (on Z) to Alternative Representations" *)
(* presented at CoqPL 2017 *)

From mathcomp Require Import ssrint ssrnum ssrbool.
From Coq Require Import ZArith Psatz.
Require Import Transfer tactics iso_ssrint.

Notation "x + y" := (intZmod.addz x y).
Notation "x - y" := (x + intZmod.oppz y).
Notation "x * y" := (intRing.mulz x y).

Notation "x <= y" := (ler' x y).
Notation "x < y" := (ltr' x y).

Open Scope int_scope.

Notation "1" := 1%:Z.
Notation "2" := 2%:Z.

Close Scope int_scope.

Goal (forall x y n:int,
  ( ~ x < n /\ x <= n /\ 2 * y = x*(x+1) -> 2 * y = n*(n+1))
  /\
  (x < n /\ x <= n /\ 2 * y = x * (x+1) -> x + 1 <= n /\ 2 *(x+1+y) = (x+1)*(x+2))).
Proof.
  intros.
  transfer.
  simpl (f _).
  psatz Z 3.
Qed.
