(* Apply a theorem modulo isomorphism *)
(* Copyright Théo Zimmermann 2015
 * This Source Code Form is subject to the terms of the Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file, You can obtain one at
 * http://mozilla.org/MPL/2.0/.
 *)

From Coq Require Import Program.Basics CMorphisms.

Set Universe Polymorphism.

(** Make the implicit argument of all maximally inserted for shorter
    morphism declarations. *)
Arguments all {A}.

(** Universe-polymorphic forall_def and arrow are not declared as opaque in the library *)
Typeclasses Opaque forall_def arrow.

Generalizable Variables A B C D.

Definition respectful_arrow `(R : A -> B -> Type) `(R' : C -> D -> Type) (f : A -> C) (f' : B -> D) :=
  forall e e', R e e' -> R' (f e) (f' e').

Notation " R ##> R' " := (respectful_arrow R R')
                           (right associativity, at level 55) : type_scope.

Class Related `(R : A -> B -> Type) (t : A) (t' : B) :=
  is_related : R t t'.

(* Strict subrelation *)
Class HeteroSubrel `(R : A -> B -> Type) (R' : A -> B -> Type) :=
  is_heteroSubrel : forall {x y}, R x y -> R' x y.

Tactic Notation "exactm" constr(t) :=
  exact ((_ : Related impl _ _) t).

Tactic Notation "applym" constr(t) :=
  let H := fresh in
  pose (H := t);
  apply ((_ : Related impl _ _)) in H;
  lazy beta delta [ id ] in H;
  apply H;
  clear H.

Tactic Notation "transfer" :=
  notypeclasses refine ((_ : Related impl _ _) _);
  [ typeclasses eauto |];
  lazy beta delta [ id ].

Tactic Notation "exactm'" constr(t) :=
  exact ((_ : Related arrow _ _) t).

Tactic Notation "applym'" constr(t) :=
  let H := fresh in
  pose (H := t);
  apply ((_ : Related arrow _ _)) in H;
  lazy beta delta [ id ] in H;
  apply H;
  clear H.

Tactic Notation "transfer'" :=
  notypeclasses refine ((_ : Related arrow _ _) _);
  [ typeclasses eauto |];
  lazy beta delta [ id ].

(* RULES *)

(* SUBREL *)

Instance subrel_rule `(R : A -> B -> Type) (R' : A -> B -> Type) (t : A) (t' : B) :
  HeteroSubrel R R' ->
  Related R t t' ->
  Related R' t t' | 9.
Proof.
  unfold HeteroSubrel, Related.
  auto.
Qed.

(* LAMBDA *)

Instance lambda_rule `(R : A -> B -> Type) `(R' : C -> D -> Type) (t : A -> C) (t' : B -> D) :
  (forall (x : A) (x' : B), Related R x x' -> Related R' (t x) (t' x')) ->
  Related (R ##> R') (fun x : A => t x) (fun x' : B => t' x').
Proof.
  intros H ? ? ?. now apply H.
Qed.

(* APP *)

Instance app_rule `(R : A -> B -> Type) `(R' : C -> D -> Type)
         (f : A -> C) (f' : B -> D) (e : A) (e' : B) :
  Related (R ##> R') f f' ->
  Related R e e' ->
  Related R' (f e) (f' e') | 2.
Proof.
  intros H ?. now apply H.
Qed.

(* ARROW *)

Instance arrow_rule (R : Type -> Type -> Type) (t1 t2 t1' t2' : Type) :
  Related R (arrow t1 t2) (arrow t1' t2') ->
  Related R (t1 -> t2) (t1' -> t2') | 2.
Proof.
  easy.
Qed.

Instance impl_rule (R : Prop -> Prop -> Prop) (t1 t2 t1' t2' : Prop) :
  Related R (impl t1 t2) (impl t1' t2') ->
  Related R (t1 -> t2) (t1' -> t2') | 2.
Proof.
  easy.
Qed.

(* FORALL *)

Instance forall_rule (R : Type -> Type -> Type)
         (t1 t1' : Type) (t2 : t1 -> Type) (t2' : t1' -> Type) :
  Related R (forall_def (fun x : t1 => t2 x)) (forall_def (fun x' : t1' => t2' x')) ->
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') | 3.
Proof.
  easy.
Qed.

Instance all_rule (R : Prop -> Prop -> Prop)
         (t1 t1' : Type) (t2 : t1 -> Prop) (t2' : t1' -> Prop) :
  Related R (all (fun x : t1 => t2 x)) (all (fun x' : t1' => t2' x')) ->
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') | 3.
Proof.
  easy.
Qed.

(* Subrelations *)

Instance sub_impl_arrow : HeteroSubrel impl arrow.
Proof. easy. Qed.

Instance sub_flip_impl_flip_arrow : HeteroSubrel (flip impl) (flip arrow).
Proof. easy. Qed.

Instance sub_iff_iffT : HeteroSubrel iff iffT.
Proof. now intros ? ? []. Qed.

Instance sub_iffT_arrow : HeteroSubrel iffT arrow.
Proof. now intros ? ? []. Qed.

Instance sub_iffT_flip_arrow : HeteroSubrel iffT (flip arrow).
Proof. now intros ? ? []. Qed.

Instance sub_iff_impl : HeteroSubrel iff impl.
Proof. now intros ? ? []. Qed.

Instance sub_iff_flip_impl : HeteroSubrel iff (flip impl).
Proof. now intros ? ? []. Qed.

Instance sub_respectful_left `(R1 : A -> B -> Type) (R2 : A -> B -> Type) `(R' : C -> D -> Type) :
  HeteroSubrel R1 R2 -> HeteroSubrel (R2 ##> R') (R1 ##> R').
Proof. unfold HeteroSubrel, "##>". auto. Qed.

Instance sub_respectful_right `(R : A -> B -> Type) `(R1' : C -> D -> Type) `(R2' : C -> D -> Type) :
  HeteroSubrel R1' R2' -> HeteroSubrel (R ##> R1') (R ##> R2').
Proof. unfold HeteroSubrel, "##>". auto. Qed.

(* Predefined instances *)

Instance iffT_reflexivity : `(Related iffT A A) | 10.
Proof. easy. Qed.

Instance iff_reflexivity : `(Related iff A A) | 10.
Proof. easy. Qed.

(*
Instance true_rule : Related iff True True.

Instance false_rule : Related iff False False.
*)

Instance arrow_transfer_rule : Related (iffT ##> iffT ##> iffT) arrow arrow.
Proof. firstorder fail. Qed.

Instance impl_transfer_rule : Related (iff ##> iff ##> iff) impl impl.
Proof. firstorder fail. Qed.

Instance iff_rule : Related (iff ##> iff ##> iff) iff iff.
Proof. firstorder fail. Qed.

Instance prod_rule : Related (iffT ##> iffT ##> iffT) prod prod.
Proof. firstorder fail. Qed.

Instance and_rule : Related (iff ##> iff ##> iff) and and.
Proof. firstorder fail. Qed.

Instance or_rule : Related (iff ##> iff ##> iff) or or.
Proof. firstorder fail. Qed.

Instance eq_rule : `(Related (@eq A ##> eq ##> iff) eq eq).
Proof. now intros * ? ? -> ? ? ->. Qed.

Instance eq_reflexivity `(x : A) : Related eq x x.
Proof. easy. Qed.

Instance not_rule : Related (iff ##> iff) not not.
Proof. intros ? ? []; split; auto. Qed.
