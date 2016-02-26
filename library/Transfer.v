(* Apply a theorem modulo isomorphism *)
(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Export Program.Basics.

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

(* Strict subrelation *)
Class HeteroSubrel {A B : Type} (R R' : A -> B -> Prop) : Prop :=
  is_heteroSubrel : forall {x y}, R x y -> R' x y.

Generalizable Variables t u.
Theorem modulo `{class : Related _ _ impl t u} : t -> u.
Proof.
  intro.
  pose proof prf as prf.
  unfold impl in prf.
  tauto.
Qed.

Check modulo.

Tactic Notation "exactm" constr(t) := exact (modulo t).
Tactic Notation "applym" constr(t) :=
  let H := fresh in
  pose (H := t); apply modulo in H; apply H; clear H.
Tactic Notation "transfer" := apply modulo.

(* RULES *)

(* ENV *)

Ltac env_rule _ t t' :=
  match goal with
    | [ p : _ t t' |- _ ] => split; eexact p
  end.

Hint Extern 1 (Related ?R ?t ?t') => env_rule R t t' : typeclass_instances.

(* SUBREL *)

Instance subrel_rule
  (A B : Type)
  (R R' : A -> B -> Prop)
  (t : A) (t' : B)
  (subrel_inst : HeteroSubrel R R')
  (inst : Related R t t') :
  Related R' t t' | 1 :=
  { prf := is_heteroSubrel prf }.

(* LAMBDA *)

Instance lambda_rule
  (A B C D : Type)
  (R : A -> B -> Prop) (R' : C -> D -> Prop)
  (t : A -> C) (t' : B -> D)
  (inst : forall (x : A) (x' : B), R x x' -> Related R' (t x) (t' x')) :
  Related (R ##> R') (fun x : A => t x) (fun x' : B => t' x') | 3 :=
  { prf := fun (x : A) (x' : B) (H : R x x') => @prf _ _ _ _ _ (inst x x' H) }.

Hint Extern 0 (Related _ _ _) => progress intros : typeclass_instances.

(* APP *)
Instance app_rule
  (A B C D : Type)
  (R : A -> B -> Prop) (R' : C -> D -> Prop)
  (f : A -> C) (f' : B -> D) (e : A) (e' : B)
  (inst_f : Related (R ##> R') f f') (inst_e : Related R e e') :
  Related R' (f e) (f' e') | 2 :=
  { prf := (@prf _ _ _ _ _ inst_f) e e' (@prf _ _ _ _ _ inst_e) }.

(* ARROW *)

Instance arrow_rule
  (R : Prop -> Prop -> Prop)
  (t1 t2 t1' t2' : Prop)
  (inst : Related R (impl t1 t2) (impl t1' t2')) :
  Related R (t1 -> t2) (t1' -> t2') | 2.
Proof. unfold impl; exact inst. Qed.

(* FORALL *)
Instance forall_rule
  (R : Prop -> Prop -> Prop)
  (t1 t1' : Type) (t2 : t1 -> Prop) (t2' : t1' -> Prop)
  (inst : Related R (all (fun x : t1 => t2 x)) (all (fun x' : t1' => t2' x'))) :
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') | 3.
Proof. unfold all; exact inst. Qed.

(* Check modulo. launches an infinite loop *)

(* Subrelations *)

Instance sub_iff_impl : HeteroSubrel iff impl.
Proof. unfold HeteroSubrel ; tauto. Qed.

Instance sub_iff_flip_impl : HeteroSubrel iff (flip impl).
Proof. unfold HeteroSubrel; tauto. Qed.

Instance sub_respectful_left
  (A B C D : Type)
  (R1 R2 : A -> B -> Prop) (R' : C -> D -> Prop) :
  HeteroSubrel R1 R2 -> HeteroSubrel (R2 ##> R') (R1 ##> R').
Proof. unfold HeteroSubrel; unfold respectful_arrow; firstorder. Qed.

Instance sub_respectful_right
  (A B C D : Type)
  (R : A -> B -> Prop) (R1' R2' : C -> D -> Prop) :
  HeteroSubrel R1' R2' -> HeteroSubrel (R ##> R1') (R ##> R2').
Proof. unfold HeteroSubrel; unfold respectful_arrow; firstorder. Qed.

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

(* Having the following instance allows transferring many
   more theorems but prevent using "apply modulo" in the
   same way as Isabelle transfer' tactic. *)
(*
Instance impl_reflexivity : forall (A : Prop), Related impl A A.
Proof.
  related_tauto.
Qed.
*)

Instance true_rule : Related iff True True.
Proof.
  related_tauto.
Qed.

Instance impl_rule : Related (iff ##> iff ##> iff) impl impl.
Proof.
  related_tauto.
Qed.

Instance iff_rule : Related (iff ##> iff ##> iff) iff iff.
Proof.
  related_tauto.
Qed.

Instance and_rule :
  Related (iff ##> iff ##> iff) and and.
Proof.
  related_tauto.
Qed.

Instance or_rule :
  Related (iff ##> iff ##> iff) or or.
Proof.
  related_tauto.
Qed.

Instance eq_rule :
  forall (A : Type),
  Related (eq ##> eq ##> iff) (@eq A) (@eq A).
Proof.
  related_basics.
  intros x x' Hx y y' Hy; split; intro Heq.
  + rewrite <- Hx, <- Hy.
    assumption.
  + rewrite Hx, Hy.
    assumption.
Qed.

Instance eq_reflexivity :
  forall (A : Set) (x : A), Related eq x x.
Proof.
  split.
  reflexivity.
Qed.

(* How to declare surjectivity of a relation *)

Theorem surj_decl :
  forall (A B : Type) (R : A -> B -> Prop),
  (forall x' : B, exists x : A, R x x') <->
  ((R ##> impl) ##> impl) (@all A) (@all B).
Proof.
  intros A B R.
  lazy delta zeta.
  split.
  + intros Hsurj p p' Hp Hall x'.
    destruct (Hsurj x') as [x Rx].
    apply (Hp x _); trivial.
  + intros Hsurj.
    apply (Hsurj (fun _ => True) _); trivial.
    intros x x' Rx _.
    exists x; trivial.
Qed.

Theorem tot_decl :
  forall (A B : Type) (R : A -> B -> Prop),
  (forall x : A, exists x' : B, R x x') <->
  ((R ##> flip impl) ##> flip impl) (@all A) (@all B).
Proof.
  intros A B R.
  lazy delta zeta.
  split.
  + intros Htot p p' Hp Hall x.
    destruct (Htot x) as [x' Rx].
    apply (Hp _ x'); trivial.
  + intros Htot.
    apply (Htot _ (fun _ => True)); trivial.
    intros x x' Rx _.
    exists x'; trivial.
Qed.

Theorem full_tot_decl :
  forall (A B : Type) (R : A -> B -> Prop),
  (forall x' : B, exists x : A, R x x') /\
  (forall x : A, exists x' : B, R x x') ->
  ((R ##> iff) ##> iff) (@all A) (@all B).
Proof.
  intros A B R.
  lazy delta zeta.
  intros [Hsurj Htot] p p' Hp; split; intros Hall.
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

Theorem full_tot_decl_recip :
  forall (A B : Type) (R : A -> B -> Prop),
  ((R ##> iff) ##> iff) (@all A) (@all B) ->
  (forall x' : B, exists x : A, R x x') /\
  (forall x : A, exists x' : B, R x x').
Proof.
  intros * H; unfold respectful_arrow in H; split.
  + intros x'.
    apply (H (fun _ => True) (fun x' => exists x, R x x')); firstorder.
  + intros x.
    apply (H (fun x => exists x', R x x') (fun x' => True)); firstorder.
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

Theorem full_uniq_decl :
  forall (A B : Type) (R : A -> B -> Prop),
  (forall x x' y', R x x' -> R x y' -> x' = y') ->
  (forall x y y', R x y' -> R y y' -> x = y) ->
  (R ##> R ##> iff) eq eq.
Proof.
  intros A B R Hfun Hinj x x' relx y y' rely.
  split; intro eq.
  + apply (Hfun x); trivial.
    now rewrite eq.
  + apply (Hinj x y y'); trivial.
    now rewrite <- eq.
Qed.

Theorem full_uniq_decl_recip :
  forall (A B : Type) (R : A -> B -> Prop),
  (R ##> R ##> iff) eq eq ->
  (forall x x' y', R x x' -> R x y' -> x' = y') /\
  (forall x y y', R x y' -> R y y' -> x = y).
Proof.
  intros A B R Huniq; lazy beta delta in Huniq; split; intros * rel1 rel2.
  + generalize (eq_refl x).
    now apply Huniq.
  + generalize (eq_refl y').
    now apply Huniq.
Qed.

