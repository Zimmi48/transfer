(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Export Transfer.Respectful.

Lemma arrow_arrow : (iffT ##> iffT ##> iffT) arrow arrow.
Proof.
(*  firstorder. *)
  intros A B [f f'] C D [g g'].
  split; intros H1 H2.
  exact (g (H1 (f' H2))).
  exact (g' (H1 (f H2))).
Qed.

Lemma iff_iff : (iff ##> iff ##> iffT) iff iff.
Proof.
  firstorder.
Qed.

Lemma and_and : (iff ##> iff ##> iffT) and and.
Proof.
  firstorder.
Qed.

Lemma or_or : (iff ##> iff ##> iffT) or or.
Proof.
  firstorder.
Qed.

Lemma eq_eq (A : Type) : (eq ##> eq ##> iffT) (@eq A) (@eq A).
Proof.
  lazy beta delta.
  intros x x' Hx y y' Hy; split; intro Heq.
  now rewrite <- Hx, <- Hy.
  now rewrite Hx, Hy.
Qed.