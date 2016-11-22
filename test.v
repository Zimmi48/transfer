
Require Export Coq.Program.Basics Coq.Classes.CMorphisms.

Set Universe Polymorphism.

Typeclasses Opaque forall_def arrow flip.
(** universe-polymorphic forall_def and arrow are not declared as opaque in the library *)

Class Related {A A' : Type} (R : A -> A' -> Type) (t : A) (t' : A') :=
  is_related : R t t'.

Instance arrow_refl : forall (T : Type), Related arrow T T | 0.
Proof.
  lazy beta delta.
  tauto.
Defined.

(*
Instance flip_rule : forall (A A' : Type) (R : A -> A' -> Type) (t : A) (t' : A'),
    Related R t t' ->
    Related (flip R) t' t.
Proof.
  lazy beta delta.
  tauto.
Defined.

Instance flip_rule' : forall (A A' : Type) (R : A -> A' -> Prop) (t : A) (t' : A'),
    Related R t t' ->
    Related (flip R) t' t.
Proof.
  lazy beta delta.
  tauto.
Defined.
*)
Class HasProof (T : Type) := proof : T.

Hint Extern 0 (HasProof _) => lazy beta delta; shelve : typeclass_instances.

Instance apply_rule : forall (T U V : Type), HasProof T -> Related arrow U V -> Related arrow (T -> U) V.
Proof.
  lazy beta delta.
  tauto.
Defined.

Ltac apply' proof :=
  notypeclasses refine ((_ : Related arrow _ _) proof);
  unshelve typeclasses eauto.

Tactic Notation "apply" constr(x) := apply' x.

Lemma test0 : forall (A B : Prop), (A -> B) -> B.
Proof.
  intros.
  apply' H.
Abort.

Lemma test1 : forall (A B : Prop), A -> (A -> A -> B) -> B.
Proof.
  intros.
  apply' H0.
  all: [> assumption | assumption ].
Defined.

Eval compute in test1.

Instance arrow_trans : forall (T U V : Type),
    Related arrow T U ->
    Related arrow U V ->
    Related arrow T V | 100000.
Proof.
  lazy beta delta.
  tauto.
Defined.

Instance and_proj1 : forall (P P' Q : Prop),
    Related arrow P P' ->
    Related arrow (P /\ Q) P'.
Proof.
  lazy beta delta.
  tauto.
Defined.

Instance and_proj2 : forall (P Q Q' : Prop),
    Related arrow Q Q' ->
    Related arrow (P /\ Q) Q'.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Unfold iff : typeclass_instances.

Hint Cut [(_*) arrow_trans arrow_trans] : typeclass_instances.

Lemma test2 : forall (A B : Prop), A -> (A <-> B) -> B.
Proof.
  intros.
  apply' H0.
  assumption.
Defined.

Eval compute in test2.

Lemma test3 : forall (A B : Prop), B -> (B -> A <-> B) -> A.
Proof.
  intros.
  apply' H0.
  all: [> assumption | assumption ].
Defined.

Eval compute in test3.

(*
Definition respectful_arrow
  {A B C D: Type}
  (R : A -> B -> Type) (R' : C -> D -> Type)
  (f : A -> C) (f' : B -> D) : Type :=
  forall e e', R e e' -> R' (f e) (f' e').

Notation " R ==> R' " :=
  (respectful_arrow R R')
    (right associativity, at level 55) : type_scope.

Instance app_rule :
  forall (A A' B B' : Type) (R : A -> B -> Type) (R' : A' -> B' -> Type)
    (f : A -> A') (g : B -> B') (t : A) (u : B),
  Related (R ==> R') f g ->
  Related R t u ->
  Related R' (f t) (g u).
Proof.
  lazy beta delta.
  intros * Hfun Harg.
  exact (Hfun _ _ Harg).
Defined.

(*
Instance eq_sym : forall (A : Type) (x y : A),
    Related eq x y ->
    Related eq y x.
Proof.
  easy.
Defined.
*)

Instance eq_sym : forall (A : Type),
  Related (flip eq ==> @eq A ==> arrow) eq eq.
Proof.
  lazy beta delta.
  intros * H1 * H2 H3.
  refine (eq_trans _ H2).
  refine (eq_trans _ H3).
  exact H1.
Qed.
*)

Instance eq_sym : forall (A : Type) (x y : A), Related arrow (x = y) (y = x).
Proof.
  exact eq_sym.
Defined.

Lemma test4 : 0 = 1 -> 1 = 0.
  intros.
  apply' H.
Defined.

Eval lazy beta delta [test4 eq_sym] in test4.
