(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

From Transfer Require Import Transfer.
From Coq Require Import Program.Basics CMorphisms.

Generalizable Variables A B.

Set Warnings "-notation-overridden".
Local Notation " A <-> B " := (iffT A B) : type_scope.
Set Warnings "default".

(** * Totality declarations *)

(** Surjectivity, i.e. right-totality *)
Definition righttotal `(R : A -> B -> Type) := ((R ##> impl) ##> impl) all all.

(** Left-totality *)
Definition lefttotal `(R : A -> B -> Type) := ((R ##> flip impl) ##> flip impl) all all.

(** Both right and left-totality *)
Definition bitotal `(R : A -> B -> Type) := ((R ##> iff) ##> iff) all all.

(** * Uniqueness declarations *)

(** Functionality, i.e. right-uniqueness *)
Definition rightunique `(R : A -> B -> Type) := (R ##> R ##> impl) eq eq.

(** Injectivity, i.e. left-uniqueness *)
Definition leftunique `(R : A -> B -> Type) := (R ##> R ##> flip impl) eq eq.

(** Both right and left-unique *)
Definition biunique `(R : A -> B -> Type) := (R ##> R ##> iff) eq eq.

(** Definition of "bounded forall" *)
Definition ball `(subType : A -> Type) (predicate : A -> Prop) :=
  forall x, subType x -> predicate x.

(* Ltac to solve automatically some goals which just need reordering of hypotheses *)

Local Ltac apply_hyp :=
  match goal with
    [ H : _ |- _ ] => apply H
  end.

Local Ltac intro_and_apply :=
  apply_hyp + (intros ? * ; intro_and_apply).

Local Ltac flipdecl := 
  lazy beta delta;
  repeat (
      repeat split;
      repeat intro_and_apply
    ).

(** * Totality declarations *)

(** ** Straightforward properties *)

Lemma fliptotal `(R : A -> B -> Type) :
  righttotal (flip R) <-> lefttotal R.
Proof. flipdecl. Qed.

Lemma flipbitotal `(R : A -> B -> Type) :
  bitotal (flip R) <-> bitotal R.
Proof. flipdecl. Qed.

Lemma bitotal_from_right_and_left_total `(R : A -> B -> Type) :
  righttotal R -> lefttotal R -> bitotal R.
Proof. flipdecl. Qed.

(** ** More complex properties *)

Theorem righttotal_decl `(R : A -> B -> Type) :
  (forall x' : B, { x : A & R x x'}) -> righttotal R.
Proof.
  lazy delta zeta.
  intros Hsurj p p' Hp Hall x'.
  destruct (Hsurj x') as [x Rx].
  now apply (Hp x _).
Qed.

Theorem lefttotal_decl `(R : A -> B -> Type) :
  (forall x : A, { x' : B & R x x'}) -> lefttotal R.
Proof.
  intros.
  apply fliptotal.
  apply righttotal_decl.
  assumption.
Qed.

(* ? Lemma righttotal_from_bitotal : bitotal R -> righttotal R. *)

(** * Uniqueness declarations *)

(** ** Straightforward properties *)

Lemma flipunique `(R : A -> B -> Type) :
  rightunique (flip R) <-> leftunique R.
Proof. flipdecl. Qed.

Lemma flipbiunique `(R : A -> B -> Type) :
  biunique (flip R) <-> biunique R.
Proof. flipdecl. Qed.

Lemma biunique_from_right_and_left_unique `(R : A -> B -> Type) :
  rightunique R -> leftunique R -> biunique R.
Proof. flipdecl. Qed.

Lemma rightunique_from_biunique `(R : A -> B -> Type) :
  biunique R -> rightunique R.
Proof. flipdecl. Qed.

Lemma leftunique_from_biunique `(R : A -> B -> Type) :
  biunique R -> leftunique R.
Proof. flipdecl. Qed.

(** ** More complex properties *)

Theorem rightunique_decl `(R : A -> B -> Type) :
  (forall x x' y', R x x' -> R x y' -> x' = y') <-> rightunique R.
Proof.
  split.
  - intros functional x x' relx y y' rely eq.
    apply (functional x); trivial.
    now rewrite eq.
  - intros rightunique x **.
    generalize (eq_refl x).
    now apply rightunique.
Qed.

Theorem bitotal_decl `(R : A -> B -> Type) :
  (forall x' : B, { x : A & R x x'}) ->
  (forall x : A, { x' : B & R x x'}) ->
  bitotal R.
Proof.
  intros righttotal lefttotal.
  apply righttotal_decl in righttotal.
  apply lefttotal_decl in lefttotal.
  now apply bitotal_from_right_and_left_total.
Qed.

Theorem leftunique_decl `(R : A -> B -> Type) :
  (forall x y y', R x y' -> R y y' -> x = y) <-> leftunique R.
Proof.
  eapply iffT_Transitive; [ | exact (flipunique _) ].
  eapply iffT_Transitive; [ | exact (rightunique_decl _) ].
  flipdecl.
Qed.

Theorem biunique_decl `(R : A -> B -> Type) :
  (forall x x' y', R x x' -> R x y' -> x' = y') ->
  (forall x y y', R x y' -> R y y' -> x = y) ->
  biunique R.
Proof.
  intros.
  apply biunique_from_right_and_left_unique.
  - now apply rightunique_decl.
  - now apply leftunique_decl.
Qed.

Theorem biunique_decl_recip1 `(R : A -> B -> Type) :
  biunique R -> forall x x' y', R x x' -> R x y' -> x' = y'.
Proof.
  intro.
  now apply rightunique_decl, rightunique_from_biunique.
Qed.

Theorem biunique_decl_recip2 `(R : A -> B -> Type) :
  biunique R -> forall x y y', R x y' -> R y y' -> x = y.
Proof.
  intros biunique *.
  apply flipbiunique in biunique.
  now apply biunique_decl_recip1 with (1 := biunique).
Qed.

Lemma generic_right_covered_decl `(R : A -> B -> Type) :
  ((R ##> impl) ##> impl) all (fun P' => forall y, { x : A & R x y } -> P' y).
Proof.
  lazy beta delta.
  intros P P' Prel HP x' (x & xrel).
  apply (Prel _ _ xrel).
  apply HP.
Qed.

Lemma generic_left_covered_decl `(R : A -> B -> Type) :    
  ((R ##> flip impl) ##> flip impl) (fun P => forall x, { y : B & R x y } -> P x) all.
Proof.
  pose proof (@generic_right_covered_decl B A (flip R)).
  lazy beta delta.
  intros P P' Prel HP x' (x & xrel).
  apply (Prel _ _ xrel).
  apply HP.
Qed.

(** *** Generic property for non-total relations *)

Theorem generic_covered_decl `(R : A -> B -> Type) :
  let coveredA := fun x => { y : B & R x y } in
  let coveredB := fun y => { x : A & R x y } in
  ((R ##> iff) ##> iff) (ball coveredA) (ball coveredB).
Proof.
  lazy beta delta zeta.
  intros P P' relP.
  split.
  - apply generic_right_covered_decl.
    firstorder.
  - apply generic_left_covered_decl.
    firstorder.
Qed.

(** ** More complex properties *)

Theorem righttotal_predicate `(R : A -> B -> Type) :
  rightunique R -> righttotal (R ##> iff).
Proof.
  intros rightunique.
  apply righttotal_decl.
  intros P'.
  exists (fun x => forall x', R x x' -> P' x').
  split; unfold arrow; firstorder.
  erewrite rightunique; eauto.
Qed.

Theorem lefttotal_predicate `(R : A -> B -> Type) :
  leftunique R -> lefttotal (R ##> iff).
Proof.
  intros * leftunique.
  apply lefttotal_decl.
  intros P.
  exists (fun x' => forall x, R x x' -> P x).
  split; unfold arrow; firstorder.
  erewrite leftunique; eauto.
Qed.

Theorem total_predicate `(R : A -> B -> Type) :
  biunique R -> bitotal (R ##> iff).
Proof.
  intros.
  apply bitotal_from_right_and_left_total.
  - now apply righttotal_predicate, rightunique_from_biunique.
  - now apply lefttotal_predicate, leftunique_from_biunique.
Qed.

Instance bitotal_predicate_rule `(R : A -> B -> Type) :
  Related (R ##> R ##> iff) eq eq ->
  Related (((R ##> iff) ##> iff) ##> iff) all all.
Proof.
  now apply total_predicate.
Qed.
