(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

From Coq Require Export Program.Basics CMorphisms.

Global Set Universe Polymorphism.

Definition respectful_arrow
  {A B C D: Type}
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) : Type :=
  forall e e', R e e' -> R' (f e) (f' e').

Notation " R ##> R' " := (respectful_arrow R R')
                           (right associativity, at level 55) : type_scope.

Lemma arrow_arrow : (iffT ##> iffT ##> iffT) arrow arrow.
Proof. firstorder. Qed.

Lemma impl_impl : (iff ##> iff ##> iff) impl impl.
Proof. firstorder. Qed.

Lemma impl_impl' : (iff ##> iff ##> iffT) impl impl.
Proof. firstorder. Qed.

Lemma iff_iff : (iff ##> iff ##> iff) iff iff.
Proof. firstorder. Qed.

Lemma iff_iff' : (iff ##> iff ##> iffT) iff iff.
Proof. firstorder. Qed.

Lemma prod_prod : (iffT ##> iffT ##> iffT) prod prod.
Proof. firstorder. Qed.

Lemma and_and : (iff ##> iff ##> iff) and and.
Proof. firstorder. Qed.

Lemma and_and' : (iff ##> iff ##> iffT) and and.
Proof. firstorder. Qed.

Lemma or_or : (iff ##> iff ##> iff) or or.
Proof. firstorder. Qed.

Lemma or_or' : (iff ##> iff ##> iffT) or or.
Proof. firstorder. Qed.

Lemma eq_eq (A : Type) : (eq ##> eq ##> iff) (@eq A) (@eq A).
Proof.
  intros x x' Hx y y' Hy; split; intro Heq.
  + rewrite <- Hx, <- Hy.
    assumption.
  + rewrite Hx, Hy.
    assumption.
Qed.

Lemma eq_eq' (A : Type) : (eq ##> eq ##> iffT) (@eq A) (@eq A).
Proof.
  lazy beta delta.
  intros x x' Hx y y' Hy; split; intro Heq.
  now rewrite <- Hx, <- Hy.
  now rewrite Hx, Hy.
Qed.