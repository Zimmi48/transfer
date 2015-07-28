Require Import MSets.MSetList.
Require Import NPeano.
Require Import Transfer.

Module Fin := Ops NPeano.Nat.
(* How to instantiate properties from MSets.MSetProperties? *)

Definition SetNat s n := Fin.cardinal s = n.

Instance empty_0 : Related SetNat Fin.empty 0.
Proof.
  split.
  reflexivity.
Qed.

Instance singleton_1 : forall x, Related SetNat (Fin.singleton x) 1.
Proof.
  split.
  reflexivity.
Qed.

Fixpoint nfirsts n :=
  match n with
  | 0 => Fin.empty
  | S n => Fin.add (n) (nfirsts n)
  end.

Instance SetNatn : forall n, Related SetNat (nfirsts n) n.
Proof.
  induction n.
  + exact empty_0.
  + simpl.
    split.
    unfold SetNat.
    (* apply cardinal_2. *)