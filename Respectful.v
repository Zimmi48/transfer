(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Export Coq.Program.Basics Coq.Classes.CMorphisms.

Set Universe Polymorphism.

Definition respectful_arrow
  {A B C D: Type}
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) : Type :=
  forall e e', R e e' -> R' (f e) (f' e').

Notation " R ##> R' " := (respectful_arrow R R')
                           (right associativity, at level 55) : type_scope.

Definition all_type {A : Type} (P : A -> Type) := forall x : A, P x.

(* How to declare surjectivity of a relation *)

Theorem surj_decl :
  forall (A B : Type) (R : A -> B -> Type),
    (forall x' : B, { x : A & R x x'}) ->
    ((R ##> arrow) ##> arrow) (@all_type A) (@all_type B).
Proof.
  intros A B R.
  lazy delta zeta.
  intros Hsurj p p' Hp Hall x'.
  destruct (Hsurj x') as [x Rx].
  apply (Hp x _); trivial.
Qed.

Theorem surj_decl_recip :
  forall (A B : Type) (R : A -> B -> Type),
    ((R ##> arrow) ##> arrow) (@all_type A) (@all_type B) ->
    (forall x' : B, { x : A & R x x'}).
Proof.
  intros A B R.
  lazy delta zeta.
  intros Hsurj.
  apply (Hsurj (fun _ => True) _); trivial.
  intros x x' Rx _.
  exists x; trivial.
Qed.

Theorem lefttotal_decl :
  forall (A B : Type) (R : A -> B -> Type),
    (forall x : A, { x' : B & R x x'}) ->
    ((R ##> flip arrow) ##> flip arrow) (@all_type A) (@all_type B).
Proof.
  intros A B R.
  lazy delta zeta.
  intros Htot p p' Hp Hall x.
  destruct (Htot x) as [x' Rx].
  apply (Hp _ x'); trivial.
Qed.

Theorem lefttotal_decl_recip :
  forall (A B : Type) (R : A -> B -> Type),
    ((R ##> flip arrow) ##> flip arrow) (@all_type A) (@all_type B) ->
    (forall x : A, { x' : B & R x x'}).
Proof.
  intros A B R.
  lazy delta zeta.
  intros Htot.
  apply (Htot _ (fun _ => True)); trivial.
  intros x x' Rx _.
  exists x'; trivial.
Qed.

Definition bitotal {A B : Type} (R : A -> B -> Type) :=
  ((R ##> iffT) ##> iffT) (@all_type A) (@all_type B).

Theorem bitotal_decl :
  forall (A B : Type) (R : A -> B -> Type),
    (forall x' : B, { x : A & R x x'}) ->
    (forall x : A, { x' : B & R x x'}) ->
    bitotal R.
Proof.
  intros A B R.
  lazy delta zeta.
  intros Hsurj Htot p p' Hp; split; intros Hall.
  + intro x'.
    destruct (Hsurj x') as [x Rx].
    apply (Hp x _); trivial.
  + intro x.
    destruct (Htot x) as [x' Rx].
    apply (Hp _ x'); trivial.
Qed.

(* other approach:
  intros A B R [Hsurj Htot].
  apply surj_decl in Hsurj.
  apply tot_decl in Htot.
  apply is_heteroSubrel in Hsurj.
  apply is_heteroSubrel in Htot.

Then a little bit of work on intersection and union of relations
and their compatibility with ##> is still needed. *)

Theorem bitotal_decl_recip1 :
  forall (A B : Type) (R : A -> B -> Type),
    bitotal R ->
    (forall x' : B, { x : A & R x x' }).
Proof.
  intros * H; unfold respectful_arrow in H; intros x'.
  apply (H (fun _ => True) (fun x' => { x : A & R x x'})); firstorder.
Qed.

Theorem bitotal_decl_recip2 :
  forall (A B : Type) (R : A -> B -> Type),
    bitotal R ->
    (forall x : A, { x' : B & R x x' }).
Proof.
  intros * H; unfold respectful_arrow in H; intros x.
  apply (H (fun x => { x' : B & R x x'}) (fun x' => True)); firstorder.
Qed.

Definition ball {A : Type} (subType : A -> Prop) (predicate : A -> Prop) :=
  forall x, subType x -> predicate x.

Theorem generic_covered_decl :
  forall (A B : Type) (R : A -> B -> Prop),
    let coveredA := fun x => exists y, R x y in
    let coveredB := fun y => exists x, R x y in
    ((R ##> iff) ##> iff) (ball coveredA) (ball coveredB).
Proof.
  intros A B R coveredA coveredB.
  lazy beta delta.
  intros P P' Prel; split.
  + intros HP x' (x & xrel).
    destruct (Prel x x' xrel) as [Prel' _].
    apply Prel'.
    apply HP.
    now exists x'.
  + intros HP' x (x' & xrel).
    destruct (Prel x x' xrel) as [_ Prel'].
    apply Prel'.
    apply HP'.
    now exists x.
Qed.

Definition biunique {A B : Type} (R : A -> B -> Type) :=
  (R ##> R ##> iffT) eq eq.

Theorem biunique_decl :
  forall (A B : Type) (R : A -> B -> Type),
    (forall x x' y', R x x' -> R x y' -> x' = y') ->
    (forall x y y', R x y' -> R y y' -> x = y) ->
    biunique R.
Proof.
  intros A B R Hfun Hinj x x' relx y y' rely.
  split; intro eq.
  + apply (Hfun x); trivial.
    now rewrite eq.
  + apply (Hinj x y y'); trivial.
    now rewrite <- eq.
Qed.

Theorem biunique_decl_recip1 :
  forall (A B : Type) (R : A -> B -> Type),
    biunique R ->
    (forall x x' y', R x x' -> R x y' -> x' = y').
Proof.
  intros A B R Huniq; lazy beta delta in Huniq; intros * rel1 rel2.
  generalize (eq_refl x).
  now apply Huniq.
Qed.

Theorem biunique_decl_recip2 :
  forall (A B : Type) (R : A -> B -> Type),
    biunique R ->
    (forall x y y', R x y' -> R y y' -> x = y).
Proof.
  intros A B R Huniq; lazy beta delta in Huniq; intros * rel1 rel2.
  generalize (eq_refl y').
  now apply Huniq.
Qed.
