(* Apply a theorem modulo isomorphism *)
(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Import Program.Basics.

Definition respectful_arrow
  {A B C D: Type}
  (R : A -> B -> Prop) (R' : C -> D -> Prop)
  (f : A -> C) (f' : B -> D) : Prop :=
  forall e e', R e e' -> R' (f e) (f' e').

Notation " R ##> R' " := (respectful_arrow R R')
  (right associativity, at level 55) : type_scope.

Class Related
  (A B : Type) (R : A -> B -> Prop) (t : A) (t' : B) : Prop :=
  { prf : R t t' }.

Arguments Related {A B} _ _ _.

Generalizable Variables t u.
Theorem modulo `{class : Related _ _ impl t u} : t -> u.
  intro.
  assert (prf := prf).
  unfold impl in prf.
  exact (prf H).
Qed.

Check modulo.

(* RULES *)

(* ENV *)

Ltac env R t t' :=
  match goal with
    | [ p : R t t' |- _ ] => split; eexact p
  end.

Hint Extern 1 (Related ?R ?t ?t') => env R t t' : typeclass_instances.

(* LAMBDA *)

Instance lambda
  (A B C D : Type)
  (R : A -> B -> Prop) (R' : C -> D -> Prop)
  (t : A -> C) (t' : B -> D)
  (inst : forall (x : A) (x' : B), R x x' -> Related R' (t x) (t' x')) :
  Related (R ##> R') (fun x : A => t x) (fun x' : B => t' x') :=
  { prf := fun (x : A) (x' : B) (H : R x x') => @prf _ _ _ _ _ (inst x x' H) }.

(*Hint Extern 0 (Related _ _ _) => progress intros : typeclass_instances.*)

(* APP *)

Instance app
  (A B C D : Type)
  (R : A -> B -> Prop) (R' : C -> D -> Prop)
  (f : A -> C) (f' : B -> D) (e : A) (e' : B)
  (inst_e : Related R e e') (inst_f : Related (R ##> R') f f') :
  Related R' (f e) (f' e') :=
  { prf := (@prf _ _ _ _ _ inst_f) e e' (@prf _ _ _ _ _ inst_e) }.

(* ARROW *)
Instance arrow_rule
  (R : Prop -> Prop -> Prop)
  (t1 t2 t1' t2' : Prop)
  (inst : Related R (impl t1 t2) (impl t1' t2')) :
  Related R (t1 -> t2) (t1' -> t2') := { prf := prf }.

(* FORALL *)
Instance forall_rule
  (R : Prop -> Prop -> Prop)
  (t1 t1' : Type) (t2 : t1 -> Prop) (t2' : t1' -> Prop)
  (inst : Related R (all (fun x : t1 => t2 x)) (all (fun x' : t1' => t2' x'))) :
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') := { prf := prf }.

(* Check modulo. launches an infinite loop *)

(* Predefined instances *)

Ltac related_basics :=
  split;
  unfold respectful_arrow;
  unfold impl;
  unfold all;
  unfold flip.

Ltac related_tauto :=
  related_basics;
  tauto.

Instance impl1 :
  Related (flip impl ##> impl ##> impl) impl impl.
Proof.
  related_tauto.
Qed.

(*
Instance impl2 : forall (A : Prop), Related impl A A.
Proof.
  related_tauto.
Qed.
*)

Instance and1 :
  Related (impl ##> impl ##> impl) and and.
Proof.
  related_tauto.
Qed.

Instance or1 :
  Related (impl ##> impl ##> impl) or or.
Proof.
  related_tauto.
Qed.