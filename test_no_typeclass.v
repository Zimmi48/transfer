Require Export Coq.Program.Basics Coq.Classes.CMorphisms.

(*Set Universe Polymorphism.*)

Lemma arrow_refl : forall (T : Type), arrow T T.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Extern 0 (arrow _ _) => refine (arrow_refl _) : related.

(*Hint Unfold flip : related.*)

(*Definition apply_to {T : Type} (U : T -> Type) (t : T) := U t.*)

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

Hint Extern 0 (arrow (forall _ : _, _) _) => refine (apply_rule _ _); [ shelve |] : related.
Hint Extern 0 (arrow (forall _ : _, _) _) => refine (apply_rule _ _); [] : related.

Ltac apply' proof :=
  refine ((_ : arrow _ _) proof);
  unshelve typeclasses eauto with nocore related.
(* Attention: typeclasses eauto even with nocore is able to use the hypotheses
   of the context. It does not here, because we immediately shelve any premise
   that we want the user to solve. But hypotheses talking about arrow could
   still influence the search. *)

Tactic Notation "apply" constr(x) := apply' x.
(* Shadowing of the old apply tactic. *)
(* The Tactic Notation is also useful for better error message when the applied
   lemma does not exist. *)

Lemma test0 : forall (A B : Prop), (A -> B) -> B.
Proof.
  intros.
  apply H.
  all:[> now_show A].
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
  (* apply nat_ind normally generates three goals but isn't this behavior better? *)
  apply nat_ind; lazy beta; swap 1 2; [| intros x IHx ].
  - apply plus_n_O.
  - intro y.
    etransitivity.
    apply plus_Sn_m.
    etransitivity.
    2: apply plus_n_Sm.
    apply f_equal.
    apply IHx.
Qed.

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

Lemma and_proj2 :
  forall (P Q Q' : Prop),
    arrow Q Q' ->
    arrow (P /\ Q) Q'.
Proof.
  lazy beta delta.
  tauto.
Defined.

Hint Resolve and_proj1 and_proj2 : related.

Hint Transparent iff : related.

Hint Cut [(_*) arrow_trans arrow_trans] : related.

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

Lemma eq_sym : forall (A : Type) (x y : A), arrow (x = y) (y = x).
Proof.
  exact eq_sym.
Defined.

Hint Resolve eq_sym : related.

Lemma test4 : 0 = 1 -> 1 = 0.
  intros.
  apply H.
Defined.

Eval lazy beta delta [test4 eq_sym] in test4.



