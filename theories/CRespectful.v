(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

From Coq Require Import CMorphisms RelationClasses.
Require Import Transfer.

Global Set Universe Polymorphism.

Set Warnings "-notation-overridden".
Local Notation " A <-> B " := (iffT A B) : type_scope.
Set Warnings "default".

Generalizable Variables A B C D.

(** * Totality declarations *)

(** Surjectivity, i.e. right-totality *)
Definition righttotal `(R : A -> B -> Type) :=
  ((R ##> arrow) ##> arrow) forall_def forall_def.

(** Left-totality *)
Definition lefttotal `(R : A -> B -> Type) :=
  ((R ##> flip arrow) ##> flip arrow) forall_def forall_def.

(** Both right and left-totality *)
Definition bitotal `(R : A -> B -> Type) :=
  ((R ##> iffT) ##> iffT) forall_def forall_def.

(** * Uniqueness declarations *)

(** Functionality, i.e. right-uniqueness *)
Definition rightunique `(R : A -> B -> Type) :=
  (R ##> R ##> arrow) eq eq.

(** Injectivity, i.e. left-uniqueness *)
Definition leftunique `(R : A -> B -> Type) :=
  (R ##> R ##> flip arrow) eq eq.

(** Both right and left-unique *)
Definition biunique `(R : A -> B -> Type) :=
  (R ##> R ##> iffT) eq eq.

(** Definition of "bounded forall" *)
Definition ball `(subType : A -> Type) (predicate : A -> Type) :=
  forall x, subType x -> predicate x.

(** ** Ltac to solve automatically some goals which just need reordering of hypotheses *)

Ltac apply_hyp :=
  match goal with
    [ H : _ |- _ ] => apply H
  end.

Ltac intro_and_apply :=
  apply_hyp + (intros ? * ; intro_and_apply).

Ltac flipdecl := 
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
  (forall x' : B, { x : A & R x x'}) <-> righttotal R.
Proof.
  lazy delta zeta.
  split; intros Hsurj.
  - intros p p' Hp Hall x'.
    destruct (Hsurj x') as [x Rx].
    now apply (Hp x _).
  - apply (Hsurj (fun _ => True) _); trivial.
    intros x x' Rx _.
    now exists x.
Qed.

Theorem lefttotal_decl `(R : A -> B -> Type) :
  (forall x : A, { x' : B & R x x'}) <-> lefttotal R.
Proof.
  eapply iffT_Transitive; [ | exact (fliptotal _) ].
  eapply iffT_Transitive; [ | exact (righttotal_decl _) ].
  reflexivity.
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

Lemma bitotal_decl_recip1 `(R : A -> B -> Type) :
  bitotal R -> (forall x' : B, { x : A & R x x' }).
Proof.
  intro bitotal.
  apply (bitotal (fun _ => True) (fun x' => { x : A & R x x'})); firstorder.
Qed.

Lemma bitotal_decl_recip2 `(R : A -> B -> Type) :
  bitotal R -> (forall x : A, { x' : B & R x x' }).
Proof.
  intro bitotal.
  apply bitotal_decl_recip1.
  apply flipbitotal.
  assumption.
Qed.

Lemma righttotal_from_bitotal `(R : A -> B -> Type) :
  bitotal R -> righttotal R.
Proof.
  intro bitotal.
  apply righttotal_decl.
  apply bitotal_decl_recip1.
  assumption.
Qed.

Lemma lefttotal_from_bitotal `(R : A -> B -> Type) :
  bitotal R -> lefttotal R.
Proof.
  intro bitotal.
  apply fliptotal.
  apply righttotal_from_bitotal.
  apply flipbitotal.
  assumption.
Qed.

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
  intro biunique.
  apply rightunique_decl.
  apply rightunique_from_biunique.
  assumption.
Qed.

Theorem biunique_decl_recip2 `(R : A -> B -> Type) :
  biunique R -> forall x y y', R x y' -> R y y' -> x = y.
Proof.
  intros biunique *.
  apply flipbiunique in biunique.
  now apply biunique_decl_recip1 with (1 := biunique).
Qed.

Lemma generic_right_covered_decl `(R : A -> B -> Type) :
  ((R ##> arrow) ##> arrow) forall_def (fun P' => forall y, { x : A & R x y } -> P' y).
Proof.
  lazy beta delta.
  intros P P' Prel HP x' (x & xrel).
  apply (Prel _ _ xrel).
  apply HP.
Qed.

Lemma generic_left_covered_decl `(R : A -> B -> Type) :
  ((R ##> flip arrow) ##> flip arrow) (fun P => forall x, { y : B & R x y } -> P x) forall_def.
Proof.
  pose (H := @generic_right_covered_decl B A (flip R)).
  lazy beta delta.
  intros P P' Prel HP x' (x & xrel).
  apply (Prel _ _ xrel).
  apply HP.
Qed.

(** *** Generic property for non-total relations *)

Theorem generic_covered_decl `(R : A -> B -> Type) :
  let coveredA := fun x => { y : B & R x y } in
  let coveredB := fun y => { x : A & R x y } in
  ((R ##> iffT) ##> iffT) (ball coveredA) (ball coveredB).
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
  rightunique R <-> righttotal (R ##> iffT).
Proof.
  split.
  - intros rightunique.
    apply righttotal_decl.
    intros P'.
    exists (fun x => forall x', R x x' -> P' x').
    (*  exists (fun x => { x' : B & prodP (R x x') (P' x') }). *)
    split; unfold arrow; firstorder.
    erewrite rightunique; eauto.
  - intros righttotal x x' relx y y' rely ->.
    assert ({ P : A -> Type & (R ##> iffT) P (eq x') }) as (P & HP)
        by now apply righttotal_decl.
    apply HP in relx.
    apply HP in rely.
    apply rely.
    apply relx.
    reflexivity.
Qed.

Theorem lefttotal_predicate `(R : A -> B -> Type) :
  leftunique R <-> lefttotal (R ##> iffT).
Proof.
  eapply iffT_Transitive; [ | exact (fliptotal _) ].
  eapply iffT_Transitive; [ symmetry; exact (flipunique _) | ].
  eapply iffT_Transitive; [ exact (righttotal_predicate _) | ].
  flipdecl.
Qed.

Theorem total_predicate `(R : A -> B -> Type) :
  biunique R <-> bitotal (R ##> iffT).
Proof.
  split.
  - intro biunique.
    apply bitotal_from_right_and_left_total;
      [ apply righttotal_predicate;
        apply rightunique_from_biunique
      | apply lefttotal_predicate;
        apply leftunique_from_biunique ];
      exact biunique.
  - intro bitotal.
    apply biunique_from_right_and_left_unique;
      [ apply righttotal_predicate;
        apply righttotal_from_bitotal
      | apply lefttotal_predicate;
        apply lefttotal_from_bitotal ];
      exact bitotal.
Qed.

Lemma rightunique_predicate `(R : A -> B -> Type) :
  righttotal R ->
  ((R ##> iffT) ##> (R ##> iffT) ##> arrow) (eq ##> iffT) (eq ##> iffT).
Proof.
  intros righttotal P P' relP Q Q' relQ H x' * <-.
  assert ({ x : A & R x x' }) as (x & Hx)
      by now apply righttotal_decl.
  pose proof Hx as Hx2.
  specialize (H x x eq_refl).
  apply relP in Hx.
  apply relQ in Hx2.
  firstorder.
Qed.

Lemma leftunique_predicate `(R : A -> B -> Type) :
  lefttotal R ->
  ((R ##> iffT) ##> (R ##> iffT) ##> flip arrow) (eq ##> iffT) (eq ##> iffT).
Proof.
  intros lefttotal.
  apply fliptotal in lefttotal.
  apply rightunique_predicate in lefttotal.
  intros P P' ? Q Q' ?.
  specialize (lefttotal P' P ltac:(flipdecl) Q' Q ltac:(flipdecl)).
  assumption.
Qed.

Lemma biunique_predicate `(R : A -> B -> Type) :
  bitotal R ->
  ((R ##> iffT) ##> (R ##> iffT) ##> iffT) (eq ##> iffT) (eq ##> iffT).
Proof.
  intro bitotal.
  pose (righttotal := righttotal_from_bitotal _ bitotal).
  pose (lefttotal := lefttotal_from_bitotal _ bitotal).
  intros P P' relP Q Q' relQ; split;
    [ apply (rightunique_predicate _ righttotal _ _ relP _ _ relQ)
    | apply (leftunique_predicate _ lefttotal _ _ relP _ _ relQ) ];
    assumption.
Qed.

(** ** A lemma that is not a generalization of the previous ones unfortunately. *)

Lemma bitotal_function `(R : A -> B -> Type) `(S : C -> D -> Type) :
  biunique R -> bitotal R -> bitotal S -> bitotal (R ##> S).
Proof.
  intros biunique_R bitotal_R bitotal_S.
  apply bitotal_decl.
  - pose (rightunique_R := biunique_decl_recip1 _ biunique_R).
    pose (lefttotal_R := bitotal_decl_recip2 _ bitotal_R).
    pose (righttotal_S := bitotal_decl_recip1 _ bitotal_S).
    intros f'.
    exists (fun x : A => projT1 (righttotal_S (f' (projT1 (lefttotal_R x))))).
    intros x x' relx.
    specialize (rightunique_R x x' (projT1 (lefttotal_R x)) relx).
    rewrite <- rightunique_R.
    + destruct (righttotal_S (f' x')); auto.
    + destruct (lefttotal_R x); auto.
  - pose (leftunique_R := biunique_decl_recip2 _ biunique_R).
    pose (righttotal_R := bitotal_decl_recip1 _ bitotal_R).
    pose (lefttotal_S := bitotal_decl_recip2 _ bitotal_S).
    intro f.
    exists (fun x' : B => projT1 (lefttotal_S (f (projT1 (righttotal_R x'))))).
    intros x x' relx.
    specialize (leftunique_R x (projT1 (righttotal_R x')) x' relx).
    rewrite <- leftunique_R.
    + destruct (lefttotal_S (f x)); auto.
    + destruct (righttotal_R x'); auto.
Qed.

(** Instances *)

Instance bitotal_predicate_rule' `(R : A -> B -> Type) :
  Related (R ##> R ##> iffT) eq eq ->
  Related (((R ##> iffT) ##> iffT) ##> iffT) forall_def forall_def.
Proof.
  unfold Related.
  intros.
  now apply total_predicate.
Qed.
