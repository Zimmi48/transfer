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

  Lemma bitotal_from_right_and_left_total : righttotal -> lefttotal -> bitotal.
  Proof.
    lazy beta delta.
    intros H1 H2 P P' relP.
    split; [ apply H1 | apply H2 ]; apply relP.
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
    now apply bitotal_from_right_and_left_total.
  Qed.

  Lemma bitotal_decl_recip1 : bitotal -> (forall x' : B, { x : A & R x x' }).
  Proof.
    intro bitotal.
    apply (bitotal (fun _ => True) (fun x' => { x : A & R x x'})); firstorder.
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
    intro bitotal.
    apply (bitotal (fun x => { x' : B & R x x'}) (fun x' => True)); firstorder.
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

  (** ** Uniqueness declarations *)

  (** Functionality, i.e. right-uniqueness *)
  Definition rightunique := (R ##> R ##> arrow) eq eq.

  (** Injectivity, i.e. left-uniqueness *)
  Definition leftunique := (R ##> R ##> flip arrow) eq eq.

  (** Both right and left-unique *)
  Definition biunique := (R ##> R ##> iffT) eq eq.

  Theorem rightunique_decl :
    (forall x x' y', R x x' -> R x y' -> x' = y') <-> rightunique.
  Proof.
    split.
    - intros functional x x' relx y y' rely eq.
      apply (functional x); trivial.
      now rewrite eq.
    - intros rightunique x **.
      generalize (eq_refl x).
      now apply rightunique.
  Qed.

  Theorem leftunique_decl :
    (forall x y y', R x y' -> R y y' -> x = y) <-> leftunique.
  Proof.
    split.
    - intros injective x x' relx y y' rely eq.
      apply (injective x y y'); trivial.
      now rewrite <- eq.
    - intros leftunique x y y' **.
      generalize (eq_refl y').
      now apply leftunique.
  Qed.

  Lemma biunique_from_right_and_left_unique : rightunique -> leftunique -> biunique.
  Proof.
    lazy beta delta.
    intros H1 H2 **.
    split; [ apply H1 | apply H2 ]; assumption.
  Qed.    
  
  Theorem biunique_decl :
    (forall x x' y', R x x' -> R x y' -> x' = y') ->
    (forall x y y', R x y' -> R y y' -> x = y) ->
    biunique.
  Proof.
    intros rightunique leftunique.
    apply rightunique_decl in rightunique.
    apply leftunique_decl in leftunique.
    now apply biunique_from_right_and_left_unique.
  Qed.

  Lemma rightunique_from_biunique : biunique -> rightunique.
  Proof.
    intros biunique x x' relx y y' rely.
    apply iffT_arrow_subrelation.
    now apply biunique.
  Qed.

  Lemma leftunique_from_biunique : biunique -> leftunique.
  Proof.
    intros biunique x x' relx y y' rely.
    apply iffT_flip_arrow_subrelation.
    now apply biunique.
  Qed.

  Theorem biunique_decl_recip1 : biunique -> forall x x' y', R x x' -> R x y' -> x' = y'.
  Proof.
    intro biunique.
    apply rightunique_decl.
    apply rightunique_from_biunique.
    exact biunique.
  Qed.

  Theorem biunique_decl_recip2 : biunique -> forall x y y', R x y' -> R y y' -> x = y.
  Proof.
    intro biunique.
    apply leftunique_decl.
    apply leftunique_from_biunique.
    exact biunique.
  Qed.

End Declarations.

Section PredicateDeclarations.

  Variables A B : Type.
  Variable R : A -> B -> Type.

  (** * Properties of predicates *)
  
  Theorem righttotal_predicate : rightunique R <-> righttotal (R ##> iffT).
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
  
  Theorem lefttotal_predicate : leftunique R <-> lefttotal (R ##> iffT).
  Proof.
    split.
    - intros leftunique.
      apply lefttotal_decl.
      intros P.
      exists (fun x' => forall x, R x x' -> P x).
      (*  exists (fun x => { x' : B & prodP (R x x') (P' x') }). *)
      split; unfold arrow; firstorder.
      erewrite leftunique; eauto.
    - intros lefttotal x x' relx y y' rely ->.
      assert ({ P' : B -> Type & (R ##> iffT) (eq x) P' }) as (P' & HP')
          by now apply lefttotal_decl.
      apply HP' in relx.
      apply HP' in rely.
      apply rely.
      apply relx.
      reflexivity.
  Qed.

  Theorem total_predicate : biunique R <-> bitotal (R ##> iffT).
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

  Lemma half_uniq_predicate :
    (forall x', { x : A & R x x' }) ->
    forall (P Q : A -> Type) (P' Q' : B -> Type),
      (eq ##> iffT) P Q -> (R ##> iffT) P P' ->
      (R ##> iffT) Q Q' -> (eq ##> iffT) P' Q'.
  Proof.
    intros H P Q P' Q' H0 H1 H2 x' y' <-.
    destruct (H x') as (x & Hx).
    pose proof Hx as Hx2.
    specialize (H0 x x eq_refl).
    apply H1 in Hx.
    apply H2 in Hx2.
    firstorder.
  Qed.

End PredicateDeclarations.

Section PredicateDeclarations'.

  Variables A B : Type.
  Variable R : A -> B -> Type.
  
  Lemma unique_predicate :
    bitotal R ->
    ((R ##> iffT) ##> (R ##> iffT) ##> iffT) (eq ##> iffT) (eq ##> iffT).
  Proof.
    intro bitotal.
    pose (Hsurj := bitotal_decl_recip1 bitotal).
    pose (Htot := bitotal_decl_recip2 bitotal).
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

End PredicateDeclarations'.