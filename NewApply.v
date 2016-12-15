Require Export Basics Morphisms.

Generalizable All Variables.

(** Related is just an identity function on the type of relations.
 ** It is used to create a dummy head-constant that will allow us to register our hints. *)
Definition Related `(R : X -> X' -> Type) := R.

(** respectful_arrow is the heterogeneous generalization of the one of the standard library *)

Definition respectful_arrow `(RX : X -> X' -> Type) `(RY : Y -> Y' -> Type) (f : X -> Y) (f' : X' -> Y') :=
  forall x x', RX x x' -> RY (f x) (f' x').

Notation " R1 ==> R2 " := (respectful_arrow R1 R2) (right associativity, at level 55) : type_scope.

(** The two main inference rules of the respectful arrow. *)

Lemma lambda_rule :
  `{ forall {f : X -> Y} {f' : X' -> Y'},
       (forall x x', RX x x' -> Related RY (f x) (f' x')) ->
       Related (RX ==> RY) (fun x => f x) (fun x' => f' x') }.
Proof.
  intros * H.
  refine H.
Defined.

Lemma app_rule :
 `{ forall {f : X -> Y} {f' : X' -> Y'},
      Related (RX ==> RY) f f' ->
      Related RX x x' ->
      Related RY (f x) (f' x') }.
Proof.
  intros * Hfun Harg.
  refine (Hfun _ _ Harg).
Defined.

Hint Resolve lambda_rule app_rule : related.

(*Hint Extern 0 => unshelve simple eapply (app_rule _ _); shelve_unifiable : related.*)
(* Why is this unshelve necessary? *)

(** Alternative inference rule for functions of two or more arguments *)

Lemma app_rule' :
 `{ forall {f : X1 -> X2 -> Y} {f' : X2' -> X1' -> Y'},
      Related (RX2 ==> RY) (f x1) (flip f' x1') ->
      Related RX2 x2 x2' ->
      Related RY (f x1 x2) (f' x2' x1') }.
Proof.
  intros * Hfun Harg.
  refine (Hfun _ _ Harg).
Defined.

Hint Resolve app_rule' : related.

(** Inference rules to change a forall or an implication for a function application *)

Lemma forall_rule :
  `{ forall {P : X -> Type} {P' : X' -> Type},
       Related R (forall_def (fun x => P x)) (forall_def (fun x' => P' x')) ->
       Related R (forall x, P x) (forall x', P' x') }.
Proof.
  intros * H.
  refine H.
Defined.

(*
(** When the terms are not symmetric *)

Lemma forall_rule' :
  `{ forall {P : X -> Type} {P' : Type},
       Related arrow (forall_def (fun x => P x)) (forall_def (fun _ : unit => P')) ->
       Related arrow (forall x, P x) P' }.
Proof.
  intros * H1 H2.
  refine (H1 H2 tt).
Defined.

Hint Resolve forall_rule forall_rule' : related.

(** The total relation between type X and unit (non-empty iff X is non-empty) *)

Definition Witness `(x : X) (_ : unit) := True.

(** The only heterogeneous rule for apply without transfer *)

Lemma find_witness : `{ X -> Related ((Witness ==> arrow) ==> arrow) (@forall_def X) (@forall_def unit) }.
Proof.
  intros ? x f f' H1 H2 ?.
  refine (H1 x _ I _).
  refine (H2 _).
Defined.

Hint Resolve find_witness : related.
*)

Lemma apply_rule :
  `{ forall (t : T),
       Related arrow (U t) V ->
       Related arrow (forall x : T, U x) V }.
Proof.
  intros *.
  lazy beta delta.
  intros H1 H2.
  apply H1.
  apply H2.
Defined.

Hint Extern 10 (Related arrow (forall _ : _, _) _) => refine (apply_rule _ _); [ shelve |] : related.
Hint Extern 10 (Related arrow (forall _ : _, _) _) => refine (apply_rule _ _); [] : related.

(** Generic transfer rules, i.e. hints with no premises (borrowing the terminology from Isabelle) *)

Lemma eq_rule : `{ Related (eq ==> eq ==> arrow) (@eq A) (@eq A) }.
Proof.
  intros ? ? ? eq1 ? ? eq2 eq3.
  refine (eq_trans _ _).
  - symmetry; refine eq1.
  - refine (eq_trans eq3 eq2).
Defined.

Lemma eq_refl' : `{ forall x : A, Related eq x x }.
Proof.
  intros.
  refine eq_refl.
Defined.

Hint Resolve eq_rule eq_refl' : related.

(** Some specific transfer rules. *)

Lemma comm_rule : `{ Related (eq ==> eq ==> eq) Nat.add (flip Nat.add) }.
Proof.
  intros ? ? -> ? ? ->.
  Require Import Arith.
  refine (Nat.add_comm _ _).
Defined.

Hint Resolve comm_rule : related.

(** Test *)

Lemma test1 : forall n m, Related arrow (forall x : nat, x = x) (n + m = m + n).
Proof.
  intros.
  typeclasses eauto with related.
(* Equivalent to:
  refine (apply_rule _ _).
  simple eapply app_rule.
  - simple eapply app_rule.
    + simple eapply eq_rule.
    + simple eapply eq_refl'.
  - simple eapply app_rule'.
    + simple eapply app_rule.
      * simple eapply comm_rule.
      * simple eapply eq_refl'.
    + simple eapply eq_refl'.
*)
Defined.

