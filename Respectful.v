(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Export Coq.Program.Basics Coq.Classes.CMorphisms.
Require Coq.Setoids.Setoid.

Global Set Universe Polymorphism.

Definition respectful_arrow
  {A B C D: Type}
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) : Type :=
  forall e e', R e e' -> R' (f e) (f' e').

Notation " R ##> R' " := (respectful_arrow R R')
                           (right associativity, at level 55) : type_scope.

Local Notation " A <-> B " := (iffT A B) : type_scope.

Section Declarations.

  Set Implicit Arguments.
  Variables A B : Type.
  Variable R : A -> B -> Type.

  (** * Totality declarations *)

  (** Surjectivity, i.e. right-totality *)
  Definition righttotal := ((R ##> arrow) ##> arrow) forall_def forall_def.

  (** Left-totality *)
  Definition lefttotal := ((R ##> flip arrow) ##> flip arrow) forall_def forall_def.

  (** Both right and left-totality *)
  Definition bitotal := ((R ##> iffT) ##> iffT) forall_def forall_def.

  Theorem righttotal_decl : (forall x' : B, { x : A & R x x'}) <-> righttotal.
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

  Theorem lefttotal_decl : (forall x : A, { x' : B & R x x'}) <-> lefttotal.
  Proof.
    lazy delta zeta.
    split; intros Htot.
    - intros p p' Hp Hall x.
      destruct (Htot x) as [x' Rx].
      now apply (Hp _ x').
    - apply (Htot _ (fun _ => True)); trivial.
      intros x x' Rx _.
      now exists x'.
  Qed.

  Lemma bitotal_from_left_and_right_total : righttotal -> lefttotal -> bitotal.
  Proof.
    lazy beta delta.
    intros H1 H2 P P' H3.
    split.
    1:apply H1.
    2:apply H2.
    all:apply H3.
  Qed.

  (* The proof could maybe be made more generic with a little bit of work on
     intersection and union of relations and their compatibility with ##> *)

  Theorem bitotal_decl :
    (forall x' : B, { x : A & R x x'}) ->
    (forall x : A, { x' : B & R x x'}) ->
    bitotal.
  Proof.
    intros righttotal lefttotal.
    apply righttotal_decl in righttotal.
    apply lefttotal_decl in lefttotal.
    now apply bitotal_from_left_and_right_total.
  Qed.

  Lemma bitotal_decl_recip1 : bitotal -> (forall x' : B, { x : A & R x x' }).
  Proof.
    intros * H; unfold respectful_arrow in H; intros x'.
    apply (H (fun _ => True) (fun x' => { x : A & R x x'})); firstorder.
  Qed.

  Lemma righttotal_from_bitotal : bitotal -> righttotal.
  Proof.
    intro bitotal.
    apply righttotal_decl.
    apply bitotal_decl_recip1.
    exact bitotal.
  Qed.

  Lemma bitotal_decl_recip2 : bitotal -> (forall x : A, { x' : B & R x x' }).
  Proof.
    intros * H; unfold respectful_arrow in H; intros x.
    apply (H (fun x => { x' : B & R x x'}) (fun x' => True)); firstorder.
  Qed.

  Lemma lefttotal_from_bitotal : bitotal -> lefttotal.
  Proof.
    intro bitotal.
    apply lefttotal_decl.
    apply bitotal_decl_recip2.
    exact bitotal.
  Qed.

  (** ** Generic property for non-total relations *)
  Definition ball {A : Type} (subType : A -> Type) (predicate : A -> Type) :=
    forall x, subType x -> predicate x.

  Theorem generic_covered_decl :
    let coveredA := fun x => { y : B & R x y } in
    let coveredB := fun y => { x : A & R x y } in
    ((R ##> iffT) ##> iffT) (ball coveredA) (ball coveredB).
  Proof.
    intros coveredA coveredB.
    lazy beta delta.
    intros P P' Prel; split.
    - intros HP x' (x & xrel).
      destruct (Prel x x' xrel) as [Prel' _].
      apply Prel'.
      apply HP.
      now exists x'.
    - intros HP' x (x' & xrel).
      destruct (Prel x x' xrel) as [_ Prel'].
      apply Prel'.
      apply HP'.
      now exists x.
  Qed.

  Definition rightunique := (R ##> R ##> arrow) eq eq.
  Definition biunique := (R ##> R ##> iffT) eq eq.

  Theorem biunique_decl :
    (forall x x' y', R x x' -> R x y' -> x' = y') ->
    (forall x y y', R x y' -> R y y' -> x = y) ->
    biunique.
  Proof.
    intros Hfun Hinj x x' relx y y' rely.
    split; intro eq.
    + apply (Hfun x); trivial.
      now rewrite eq.
    + apply (Hinj x y y'); trivial.
      now rewrite <- eq.
  Qed.

  Theorem biunique_decl_recip1 :
    biunique ->
    (forall x x' y', R x x' -> R x y' -> x' = y').
  Proof.
    intros Huniq; lazy beta delta in Huniq; intros * rel1 rel2.
    generalize (eq_refl x).
    now apply Huniq.
  Qed.

  Theorem biunique_decl_recip2 :
    biunique ->
    (forall x y y', R x y' -> R y y' -> x = y).
  Proof.
    intros Huniq; lazy beta delta in Huniq; intros * rel1 rel2.
    generalize (eq_refl y').
    now apply Huniq.
  Qed.

  Lemma half_total_predicate :
    (forall (x : A) (x' y' : B), R x x' -> R x y' -> x' = y')
    -> forall P' : B -> Type, { P : A -> Type & (R ##> iffT) P P' }.
  Proof.
    intros Hfun P'.
    exists (fun x => forall x', R x x' -> P' x').
    (*  exists (fun x => { x' : B & prodP (R x x') (P' x') }). *)
    split; unfold arrow; firstorder.
    erewrite Hfun; eauto.
  Qed.

End Declarations.

Lemma half_total_predicate_prop :
  forall {A B : Type} (R : A -> B -> Prop),
    (forall (x : A) (x' y' : B), R x x' -> R x y' -> x' = y')
    -> forall P' : B -> Prop, { P : A -> Prop & (R ##> iff) P P' }.
Proof.
  intros A B R Hfun P'.
  exists (fun x => forall x', R x x' -> P' x').
(*  exists (fun x => { x' : B & prodP (R x x') (P' x') }). *)
  split; unfold arrow; firstorder.
  erewrite Hfun; eauto.
Qed.

Lemma half_total_predicate_recip :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall P' : B -> Prop, { P : A -> Prop & (R ##> iff) P P' }) ->
    (forall (x : A) (x' y' : B), R x x' -> R x y' -> x' = y').
Proof.
  intros A B R Htot x x' y' relxx relxy.
  destruct (Htot (eq x')) as (P & HP).
  apply HP in relxx.
  apply HP in relxy.
  rewrite <- relxy.
  rewrite relxx.
  reflexivity.
Qed.

Lemma half_uniq_predicate :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall x', { x : A & R x x' }) ->
    forall (P Q : A -> Prop) (P' Q' : B -> Prop),
      (eq ##> iff) P Q -> (R ##> iff) P P' ->
      (R ##> iff) Q Q' -> (eq ##> iff) P' Q'.
Proof.
  intros A B R H P Q P' Q' H0 H1 H2 x' y' <-.
  destruct (H x') as (x & Hx).
  pose proof Hx as Hx2.
  apply H1 in Hx; rewrite <- Hx.
  apply H2 in Hx2; rewrite <- Hx2.
  now apply H0.
Qed.

Lemma half_uniq_predicate_inst (A B : Type) (R : A -> B -> Prop) :
  ((R ##> iffT) ##> iffT) (@forall_def A) (@forall_def B) ->
  ((R ##> iff) ##> (R ##> iff) ##> iffT) (eq ##> iff) (eq ##> iff).
Proof.
  intro H.
  pose (Hsurj := @bitotal_decl_recip1 _ _ _ H).
  pose (Htot := @bitotal_decl_recip2 _ _ _ H).
  intros P P' relP Q Q' relQ; split.
  + intro relPQ.
    apply (@half_uniq_predicate _ _ _ Hsurj P Q P' Q'); trivial.
  + intro relPQ.
    apply (@half_uniq_predicate _ _ _ Htot P' Q' P Q); trivial; intros x' x relx. {
      symmetry.
      now apply relP.
    }
    apply relQ in relx.
    now rewrite relx.
Qed.

Lemma half_uniq_predicate_recip :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall (P : A -> Prop) (P' Q' : B -> Prop), (R ##> iff) P P' -> (R ##> iff) P Q' -> (eq ##> iff) P' Q') ->
    forall x', exists x, R x x'.
Proof.
  intros A B R H.
  pose (P' := fun x' => exists x, R x x').
  change (forall x', P' x').
Abort.

Lemma total_predicate
  (A B : Type)
  (R : A -> B -> Type)
  (is_related : (R ##> R ##> iffT) eq eq) :
  (((R ##> iffT) ##> iffT) ##> iffT) (@forall_def (A -> Type)) (@forall_def (B -> Type)).
Proof.
  pose (Hfun := @biunique_decl_recip1 _ _ _ is_related).
  pose (Hinj := @biunique_decl_recip2 _ _ _ is_related).
  apply bitotal_decl.
  + exact (half_total_predicate R Hfun).
  + intros *.
    edestruct (half_total_predicate (flip R)) as (P' & HP'); [ intros; eapply Hinj; eauto |].
    exists P'.
    intros; split; apply HP'; assumption.
Qed.

Lemma total_predicate_prop
  (A B : Type)
  (R : A -> B -> Prop)
  (is_related : (R ##> R ##> iffT) eq eq) :
  (((R ##> iff) ##> iffT) ##> iffT) (@forall_def (A -> Prop)) (@forall_def (B -> Prop)).
Proof.
  pose (Hfun := @biunique_decl_recip1 _ _ _ is_related).
  pose (Hinj := @biunique_decl_recip2 _ _ _ is_related).
  apply bitotal_decl.
  + exact (half_total_predicate_prop R Hfun).
  + intros *.
    edestruct (half_total_predicate_prop (flip R)) as (P' & HP'); [ intros; eapply Hinj; eauto |].
    exists P'.
    intros; split; apply HP'; assumption.
Qed.
