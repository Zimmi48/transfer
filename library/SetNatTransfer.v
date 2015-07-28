Require Import MSets.
Require Import Transfer.

Module TransferProp (Import E:DecidableType)(Fin:WSetsOn E).

Module FinProp := WPropertiesOn E Fin.

Definition SetNat s n := Fin.cardinal s = n.

Instance empty_0 : Related SetNat Fin.empty 0.
Proof.
  split.
  exact FinProp.empty_cardinal.
Qed.

Instance singleton_1 : forall x, Related SetNat (Fin.singleton x) 1.
Proof.
  split.
  apply FinProp.singleton_cardinal.
Qed.

Instance anyset_cardinal : forall s, Related SetNat s (Fin.cardinal s).
Proof.
  split.
  reflexivity.
Qed.

(* Missing definition of cartesian product on MSets *)

Ltac SetNat_basics :=
  related_basics;
  unfold SetNat;
  repeat (
    let x1 := fresh "x" in
    let x2 := fresh "x" in
    let Hx := fresh "Hx" in
    intros x1 x2 Hx;
    rewrite <- Hx;
    clear Hx x2 ).

Instance subset_le : Related (SetNat ##> SetNat ##> impl) Fin.Subset le.
Proof.
  SetNat_basics.
  apply FinProp.subset_cardinal.
Qed.

(* Missing definition of strict subset *)

(*
Instance injectivity : Related (SetNat ##> SetNat ##> flip impl) eq eq.
Error:
The term "eq" has type "t -> t -> Prop" while it is expected to have type
 "Fin.t -> Fin.t -> Prop" (cannot unify "Fin.t" and "t").
*)

