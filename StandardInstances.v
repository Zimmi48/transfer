(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Export Transfer.CRespectful.

Lemma arrow_arrow : (iffT ##> iffT ##> iffT) arrow arrow.
Proof.
(*  firstorder. *)
  intros A B [f f'] C D [g g'].
  split; intros H1 H2.
  exact (g (H1 (f' H2))).
  exact (g' (H1 (f H2))).
Defined.

Lemma impl_impl : (iff ##> iff ##> iff) impl impl.
Proof. firstorder. Defined.

Lemma impl_impl' : (iff ##> iff ##> iffT) impl impl.
Proof. firstorder. Defined.

Lemma iff_iff : (iff ##> iff ##> iff) iff iff.
Proof. firstorder. Defined.

Lemma iff_iff' : (iff ##> iff ##> iffT) iff iff.
Proof. firstorder. Defined.

Lemma prod_prod : (iffT ##> iffT ##> iffT) prod prod.
Proof. firstorder. Defined.

Lemma and_and : (iff ##> iff ##> iff) and and.
Proof. firstorder. Defined.

Lemma and_and' : (iff ##> iff ##> iffT) and and.
Proof. firstorder. Defined.

Lemma or_or : (iff ##> iff ##> iff) or or.
Proof. firstorder. Defined.

Lemma or_or' : (iff ##> iff ##> iffT) or or.
Proof. firstorder. Defined.

Lemma eq_eq (A : Type) : (eq ##> eq ##> iff) (@eq A) (@eq A).
Proof.
  intros x x' Hx y y' Hy; split; intro Heq.
  + rewrite <- Hx, <- Hy.
    assumption.
  + rewrite Hx, Hy.
    assumption.
Defined.

Lemma eq_eq' (A : Type) : (eq ##> eq ##> iffT) (@eq A) (@eq A).
Proof.
  lazy beta delta.
  intros x x' Hx y y' Hy; split; intro Heq.
  now rewrite <- Hx, <- Hy.
  now rewrite Hx, Hy.
Defined.