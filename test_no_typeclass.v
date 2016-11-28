Require Export Coq.Program.Basics Coq.Classes.CMorphisms.

(*Set Universe Polymorphism.*)

(* This complex arrow_refl hint serves the following purpose:
   - arrow_refl needs to be declared w/ Hint Resolve to be mentioned in Hint Cut
   - Hint Resolve does not work modulo conversion
*)

Lemma arrow_refl : forall {T : Type}, arrow T T.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Extern 0 (arrow _ _) => refine arrow_refl : related.
(* cannot be in a Hint Cut!! *)

(*Hint Unfold flip : related.*)

Lemma apply_rule :
  forall {T V : Type} {U : T -> Type},
  forall (t : T), arrow (U t) V -> arrow (forall x : T, U x) V.
Proof.
  intros *.
  lazy beta delta.
  intros H1 H2.
  apply H1.
  apply H2.
Defined.

Hint Extern 10 (arrow (forall _ : _, _) _) => refine (apply_rule _ _); [ (*match goal with |- ?g => idtac g end;*) shelve |] : related.
Hint Extern 10 (arrow (forall _ : _, _) _) => refine (apply_rule _ _); [] : related.

Ltac apply' proof :=
  refine ((_ : arrow _ _) proof);
  unshelve typeclasses eauto with nocore related;
  shelve_unifiable.
(* Attention: typeclasses eauto even with nocore is able to use the hypotheses
   of the context. It does not here, because we immediately shelve any premise
   that we want the user to solve. But hypotheses talking about arrow could
   still influence the search. *)

Tactic Notation "apply" constr(x) := apply' x.
(* Shadowing of the old apply tactic. *)
(* The Tactic Notation is also useful for better error message when the applied
   lemma does not exist. *)

Lemma test0 : forall (A B C : Prop), (A -> B -> C) -> C.
Proof.
  intros.
  refine ((_ : arrow _ _) H);
  unshelve (
      refine (apply_rule _ _); [ match goal with |- ?g => idtac g end; shelve |];
      refine (apply_rule _ _); [ match goal with |- ?g => idtac g end; shelve |];
      refine (arrow_refl)
    );
  [ now_show A | now_show B ].
  Undo.
  apply H.
  Fail all:[> now_show A | now_show B ]. (* This should not fail. *)
  (*Grab Existential Variables.*)
  (* In 8.5 *)
Abort.

Lemma test1 : forall (A B : Prop), A -> (A -> A -> B) -> B.
Proof.
  intros.
  apply H0.
  all:[> assumption | assumption ].
Defined.

Eval compute in test1.

Lemma under_binders : forall (A : Type) (f g : A -> Type),
    (forall x : A, arrow (f x) (g x)) ->
    arrow (forall x : A, f x) (forall x : A, g x).
Proof.
  lazy beta delta.
  intros * H1 H2 *.
  refine (H1 _ _).
  refine (H2 _).
Defined.

Hint Resolve under_binders : related.

Lemma test_add_comm : forall (x y : nat), x + y = y + x.
Proof.
  (* not the same behavior because not the same unification algorithm *)
  apply nat_ind; lazy beta; swap 1 2; [| intros x IHx ].
  - simpl.
    apply plus_n_O.
  - intro y.
    apply eq_trans; swap 1 2.
    + apply plus_Sn_m.
    + apply eq_trans; swap 1 2.
      * apply f_equal.
        apply IHx.
      * apply plus_n_Sm.
Qed.

Lemma arrow_trans :
  forall {T U V : Type},
    arrow T U ->
    arrow U V ->
    arrow T V.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve arrow_trans | 100000 : related.

Hint Cut [(_*) (arrow_trans) (arrow_trans)] : related.

(*
Lemma and_proj1 :
  forall (P P' Q : Prop),
    arrow P P' ->
    arrow (P /\ Q) P'.
Proof.
  lazy beta delta.
  tauto.
Defined.

Lemma and_proj2 :
  forall (P Q Q' : Prop),
    arrow Q Q' ->
    arrow (P /\ Q) Q'.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve and_proj1 and_proj2 : related.
*)

(* proj1 cannot be used as a hint with Hint Resolve *)
Hint Extern 0 (arrow (_ /\ _) _) => refine (@proj1 _ _) : related.
Hint Extern 0 (arrow (_ /\ _) _) => refine (@proj2 _ _) : related.

(*Hint Transparent iff : related.*)
(* This transparency hint apparently does not work for patterns *)
Hint Extern 0 (arrow (_ <-> _) _) => refine (@proj1 _ _) : related.
Hint Extern 0 (arrow (_ <-> _) _) => refine (@proj2 _ _) : related.

Lemma test2 : forall (A B : Prop), A -> (A <-> B) -> B.
Proof.
  intros.
  apply H0.
  assumption.
Defined.

Eval compute in test2.

Lemma test3 : forall (A B : Prop), B -> (B -> A <-> B) -> A.
Proof.
  intros.
  apply H0.
  all: [> assumption | assumption ].
Defined.

Eval compute in test3.

Lemma test4 : forall (A B : Prop), B -> (B -> A /\ B) -> A.
Proof.
  intros.
  apply H0.
  all: [> assumption ].
Defined.

Eval compute in test4.

Hint Extern 0 (arrow (_ = _) (_ = _)) => refine (@eq_sym _ _ _) : related.

Lemma test5 : 0 = 1 -> 1 = 0.
  intros.
  apply H.
Defined.

Eval lazy beta delta [test5 eq_sym] in test5.

(* Now we would like to handle SSReflect's style "reflect" *)
Require Import Bool.

Coercion is_true b := b = true.

Inductive reflect (P : Prop) (b : bool) :=
| reflect_cons : (P -> b) -> (b -> P) -> reflect P b.

Lemma reflect_to_is_false :
  forall {P : Prop} {b : bool},
    reflect P b ->
    arrow (~ P) (negb b).
Proof.
  intros P b Hreflect HnP.
  inversion Hreflect.
  destruct b.
  absurd P; trivial.
  apply H0; reflexivity.
  reflexivity.
Qed.

Lemma reflect_to_is_true :
  forall {P : Prop} {b : bool},
    reflect P b ->
    arrow P b.
Proof.
  intros * H; inversion H; trivial.
Qed.

Lemma reflect_from_is_true :
  forall {P : Prop} {b : bool},
    reflect P b ->
    arrow b P.
Proof.
  intros * H; inversion H; trivial.
Qed.

Lemma reflect_from_is_false :
  forall {P : Prop} {b : bool},
    reflect P b ->
    arrow (negb b) (~ P).
Proof.
  intros P b Hreflect Hnb HP.
  inversion Hreflect.
  rewrite H in Hnb; trivial; simpl in Hnb.
  discriminate.
Qed.

Hint Resolve reflect_from_is_false reflect_from_is_true reflect_to_is_false reflect_to_is_true : related.

Lemma andb_view : forall (b1 b2 : bool), reflect (b1 /\ b2) (b1 && b2).
Proof.
  split.
  - now intros [-> ->].
  - now destruct b1, b2.
Qed.

Lemma orb_view : forall (b1 b2 : bool), reflect (b1 \/ b2) (b1 || b2).
Proof.
  split.
  - intros [-> | ->].
    + refine (orb_true_l _).
    + refine (orb_true_r _).
  - intros; destruct b1, b2; simpl in *; auto.
Qed.

Hint Resolve andb_view orb_view : related.

Lemma test6 : true || false.
  apply or_intror; now_show false.
  Undo.
  apply or_introl; now_show true.
  easy.
Qed.