(* Apply a theorem modulo isomorphism *)
(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

Require Export Transfer.StandardInstances.

Typeclasses Opaque forall_def arrow.
(** universe-polymorphic forall_def and arrow are not declared as opaque in the library *)

Class Related
  (A B : Type) (R : A -> B -> Type) (t : A) (t' : B) : Prop :=
  is_related : R t t'.

Arguments Related {A B} _ _ _.

(* Strict subrelation *)
Class HeteroSubrel {A B : Type} (R R' : A -> B -> Type) : Prop :=
  is_heteroSubrel : forall {x y}, R x y -> R' x y.

Generalizable Variables t u.
Theorem modulo `{class : Related _ _ arrow t u} : t -> u.
Proof.
  lazy beta delta in class.
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
    | [ p : _ t t' |- _ ] => eexact p
  end.

Hint Extern 1 (Related ?R ?t ?t') => env_rule R t t' : typeclass_instances.

(* SUBREL *)

Instance subrel_rule
  (A B : Type)
  (R R' : A -> B -> Type)
  (t : A) (t' : B)
  (subrel_inst : HeteroSubrel R R')
  (inst : Related R t t') :
  Related R' t t' | 9 :=
  { is_related := is_heteroSubrel is_related }.

(* LAMBDA *)

Instance lambda_rule
  (A B C D : Type)
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (t : A -> C) (t' : B -> D)
  (inst : forall (x : A) (x' : B), R x x' -> Related R' (t x) (t' x')) :
  Related (R ##> R') (fun x : A => t x) (fun x' : B => t' x') | 3 :=
  { is_related := fun (x : A) (x' : B) (H : R x x') => @is_related _ _ _ _ _ (inst x x' H) }.

Hint Extern 0 (Related _ _ _) => progress intros ** : typeclass_instances.

(* APP *)

Instance app_rule
  (A B C D : Type)
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) (e : A) (e' : B)
  (inst_f : Related (R ##> R') f f') (inst_e : Related R e e') :
  Related R' (f e) (f' e') | 2 :=
  { is_related := (@is_related _ _ _ _ _ inst_f) e e' (@is_related _ _ _ _ _ inst_e) }.

(* ARROW *)

Instance arrow_rule
         (R : Type -> Type -> Type)
         (t1 t2 t1' t2' : Type)
         (inst : Related R (arrow t1 t2) (arrow t1' t2')) :
  Related R (t1 -> t2) (t1' -> t2') | 2 := inst.

(* FORALL *)

Instance forall_rule
  (R : Type -> Type -> Type)
  (t1 t1' : Type) (t2 : t1 -> Type) (t2' : t1' -> Type)
  (inst : Related R (forall_def (fun x : t1 => t2 x)) (forall_def (fun x' : t1' => t2' x'))) :
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') | 3 := inst.

(* Check modulo. launches an infinite loop *)

(* Subrelations *)

Instance sub_iffT_arrow : HeteroSubrel iffT arrow.
Proof. firstorder. Qed.

Instance sub_iffT_flip_arrow : HeteroSubrel iffT (flip arrow).
Proof. firstorder. Qed.

Instance sub_respectful_left
  (A B C D : Type)
  (R1 R2 : A -> B -> Type) (R' : C -> D -> Type) :
  HeteroSubrel R1 R2 -> HeteroSubrel (R2 ##> R') (R1 ##> R').
Proof. firstorder. Qed.

Instance sub_respectful_right
  (A B C D : Type)
  (R : A -> B -> Type) (R1' R2' : C -> D -> Type) :
  HeteroSubrel R1' R2' -> HeteroSubrel (R ##> R1') (R ##> R2').
Proof. firstorder. Qed.

(* Predefined instances *)

Ltac related_basics :=
  intros;
  unfold Related;
  unfold respectful_arrow;
  unfold arrow;
  unfold impl;
  unfold forall_def;
  unfold flip.

Ltac related_tauto :=
  related_basics;
  tauto.

(* Having the following instance allows transferring many
   more theorems but prevents using the transfer and applym tactics. *)
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

Instance arrow_transfer_rule : Related (iffT ##> iffT ##> iffT) arrow arrow.
Proof arrow_arrow.

Instance iff_rule : Related (iff ##> iff ##> iffT) iff iff.
Proof iff_iff.

Instance and_rule :
  Related (iff ##> iff ##> iffT) and and.
Proof and_and.

Instance or_rule :
  Related (iff ##> iff ##> iffT) or or.
Proof or_or.

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

Instance eq_rule' :
  forall (A : Type),
  Related (eq ##> eq ##> iffT) (@eq A) (@eq A).
Proof eq_eq.

Instance eq_reflexivity :
  forall (A : Set) (x : A), Related eq x x.
Proof. reflexivity. Qed.

Instance total_predicate_rule
  (A B : Type)
  (R : A -> B -> Type)
  (inst : Related (R ##> R ##> iffT) eq eq) :
  Related (((R ##> iffT) ##> iffT) ##> iffT) (@forall_def (A -> Type)) (@forall_def (B -> Type)).
Proof.
  unfold Related in *.
  now apply total_predicate.
Qed.
