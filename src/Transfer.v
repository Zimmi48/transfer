(* Copyright Théo Zimmermann 2015-2017
 * This Source Code Form is subject to the terms of the
 * Mozilla Public License, v.2.0.
 * If a copy of the MPL was not distributed with this file,
 * You can obtain one at http://mozilla.org/MPL/2.0/.
 *)

From Coq Require Import Program.Basics CMorphisms.

(*Set Universe Polymorphism.*)

Class Related {A B : Type} (R : A -> B -> Type) (t : A) (t' : B) :=
  is_related : R t t'.

Ltac transfer := 
  notypeclasses refine (proj1 (_ : Related iff _ _) _);
  [ typeclasses eauto | ];
  lazy beta; unfold id.

Definition respectful_arrow
  {X Y X' Y' : Type}
  (RX : X -> X' -> Type) (RY : Y -> Y' -> Type)
  (f : X -> Y) (f' : X' -> Y') : Type :=
  forall (x : X) (x' : X'), RX x x' -> RY (f x) (f' x').

Notation " RX ##> RY " :=
  (respectful_arrow RX RY)
    (right associativity, at level 55) : type_scope.

(* LAMBDA *)

Instance lambda_rule
  (A B C D : Type)
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (t : A -> C) (t' : B -> D) :
  (forall (x : A) (x' : B), Related R x x' -> Related R' (t x) (t' x')) ->
  Related (R ##> R') (fun x : A => t x) (fun x' : B => t' x').
Proof.
  intros H ? ? ?. now apply H.
Qed.

(* Hint Extern 0 (Related _ _ _) => progress intros ** : typeclass_instances. *)
(* You can't give this rule and not desactivating automatics intros without
   a search-space blow up *)

(* APP *)

Instance app_rule
  (A B C D : Type)
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) (e : A) (e' : B) :
  Related (R ##> R') f f' ->
  Related R e e' ->
  Related R' (f e) (f' e') | 2.
Proof.
  intros H ?. now apply H.
Qed.

(* ARROW *)

Instance impl_rule
  (R : Prop -> Prop -> Prop)
  (t1 t2 t1' t2' : Prop) :
  Related R (impl t1 t2) (impl t1' t2') ->
  Related R (t1 -> t2) (t1' -> t2') | 2.
Proof.
  easy.
Qed.

(* FORALL *)

(* How to make sure it's applied only on dependent products?  *)

Instance all_rule
  (R : Prop -> Prop -> Prop)
  (t1 t1' : Type) (t2 : t1 -> Prop) (t2' : t1' -> Prop) :
  Related R (all (fun x : t1 => t2 x)) (all (fun x' : t1' => t2' x')) ->
  Related R (forall x : t1, t2 x) (forall x' : t1', t2' x') | 3.
Proof.
  easy.
Qed.

(* FLIP *)

(* I can give to this rule a priority lower than app_rule but what I'd really like
   to use would be some kind of cut operator *)

Instance flip_rule
  (A B : Type)
  (R : A -> B -> Prop) (t : A) (u : B) :
  Related R t u ->
  Related (flip R) u t | 0.
Proof.
  easy.
Qed.

Typeclasses Opaque flip.

(* Generic transfer rules *)

Instance impl_transfer_rule : Related (flip impl ##> impl ##> impl) impl impl.
Proof.
  lazy beta delta.
  tauto.
Qed.

Instance iff_transfer_rule' : Related (iff ##> iff ##> iff) impl impl.
Proof.
  lazy beta delta.
  tauto.
Qed.
