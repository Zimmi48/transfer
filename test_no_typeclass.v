
Require Export Coq.Program.Basics Coq.Classes.CMorphisms.

Set Universe Polymorphism.

(*Typeclasses Opaque forall_def arrow flip.*)
(** universe-polymorphic forall_def and arrow are not declared as opaque in the library *)

Lemma arrow_refl : forall (T : Type), arrow T T.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve arrow_refl | 0 : related.

Lemma flip_rule :
  forall (A A' : Type) (R : A -> A' -> Type) (t : A) (t' : A'),
    R t t' ->
    (flip R) t' t.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve flip_rule : related.

Inductive HasProof (T : Type) := proof : T -> HasProof T.

Hint Extern 0 (HasProof _) => split; shelve : related.

Lemma apply_rule : forall (T U V : Type), HasProof T -> arrow U V -> arrow (T -> U) V.
Proof.
  intros ? ? ? [].
  lazy beta delta.
  tauto.
Defined.

Hint Resolve apply_rule : related.

Ltac apply' proof :=
  notypeclasses refine ((_ : arrow _ _) proof);
  unshelve typeclasses eauto with nocore related.

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
  all:[> assumption | assumption].
Defined.

Eval compute in test1.

Lemma arrow_trans :
  forall (T U V : Type),
    arrow T U ->
    arrow U V ->
    arrow T V.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve arrow_trans | 100000 : related.

Lemma and_proj1 :
  forall (P P' Q : Prop),
    arrow P P' ->
    arrow (P /\ Q) P'.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve and_proj1 : related.

Lemma and_proj2 :
  forall (P Q Q' : Prop),
    arrow Q Q' ->
    arrow (P /\ Q) Q'.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve and_proj2 : related.

Hint Unfold iff : related.

Hint Cut [(_*) arrow_trans (_*) arrow_trans] : related.

Lemma test2 : forall (A B : Prop), A -> (A <-> B) -> B.
Proof.
  intros.
  Typeclasses eauto := debug.
  Fail apply' H0.
  assumption.
Defined.

Eval compute in test2.

Lemma test3 : forall (A B : Prop), B -> (B -> A <-> B) -> A.
Proof.
  intros.
  apply' H0; assumption.
Defined.

Eval compute in test3.

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

Lemma test4 : 0 = 1 -> 1 = 0.
  intros.
  Typeclasses eauto := debug.
  Fail apply' H.

