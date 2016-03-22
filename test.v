Require Import Transfer.Transfer.
Require Coq.Setoids.Setoid.

Set Universe Polymorphism.

Lemma half_total_predicate :
  forall {A B : Type} (R : A -> B -> Prop),
    (forall (x : A) (x' y' : B), R x x' -> R x y' -> x' = y')
    -> forall P' : B -> Type, { P : A -> Type & (R ##> iffT) P P' }.
Proof.
  intros A B R Hfun P'.
  exists (fun x => forall x', R x x' -> P' x').
(*  exists (fun x => { x' : B & prodP (R x x') (P' x') }). *)
  split; unfold arrow; firstorder.
  erewrite Hfun; eauto.
Qed.

Lemma half_total_predicate_recip :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall P' : B -> Prop, { P : A -> Prop & (R ##> iff) P P' }) ->
    (forall (x : A) (x' y' : B), R x x' -> R x y' -> x' = y').
Proof.
  intros A B R Htot x x' y' relxx relxy.
  destruct (Htot (eq x')) as (P & HP).
  apply HP in relxx.
  apply HP in relxy.
  rewrite <- relxy.
  rewrite relxx.
  reflexivity.
Qed.

Lemma half_uniq_predicate :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall x', { x : A & R x x' }) ->
    forall (P Q : A -> Prop) (P' Q' : B -> Prop),
      (eq ##> iff) P Q -> (R ##> iff) P P' ->
      (R ##> iff) Q Q' -> (eq ##> iff) P' Q'.
Proof.
  intros A B R H P Q P' Q' H0 H1 H2 x' y' <-.
  destruct (H x') as (x & Hx).
  pose proof Hx as Hx2.
  apply H1 in Hx; rewrite <- Hx.
  apply H2 in Hx2; rewrite <- Hx2.
  now apply H0.
Qed.

Instance half_uniq_predicate_inst (A B : Type) (R : A -> B -> Prop) :
  (Related ((R ##> iffT) ##> iffT) (@all_type A) (@all_type B)) ->
  Related ((R ##> iff) ##> (R ##> iff) ##> iffT) (eq ##> iff) (eq ##> iff).
Proof.
  intro.
  pose (Hsurj := bitotal_decl_recip1 _ _ _ is_related).
  pose (Htot := bitotal_decl_recip2 _ _ _ is_related).
  intros P P' relP Q Q' relQ; split.
  + intro relPQ.
    apply (half_uniq_predicate _ _ _ Hsurj P Q P' Q'); trivial.
  + intro relPQ.
    apply (half_uniq_predicate _ _ _ Htot P' Q' P Q); trivial; intros x' x relx. {
      symmetry.
      now apply relP.
    }
    apply relQ in relx.
    now rewrite relx.
Qed.

Lemma half_uniq_predicate_recip :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall (P : A -> Prop) (P' Q' : B -> Prop), (R ##> iff) P P' -> (R ##> iff) P Q' -> (eq ##> iff) P' Q') ->
    forall x', exists x, R x x'.
Proof.
  intros A B R H.
  pose (P' := fun x' => exists x, R x x').
  change (forall x', P' x').
Abort.

Instance total_predicate
  (A B : Type)
  (R : A -> B -> Prop)
  (inst : Related (R ##> R ##> iff) eq eq) :
  Related (((R ##> iffT) ##> iffT) ##> iffT) (@all_type (A -> Type)) (@all_type (B -> Type)).
Proof.
  pose (Hfun := biunique_decl_recip1 _ _ _ is_related).
  pose (Hinj := biunique_decl_recip2 _ _ _ is_related).
  apply bitotal_decl.
  + exact (half_total_predicate _ Hfun).
  + intros *.
    edestruct (half_total_predicate (flip R)) as (P' & HP'); [ intros; eapply Hinj; eauto |].
    exists P'.
    intros; split; apply HP'; assumption.
Qed.

Require Import Coq.Arith.PeanoNat.
Require Import Transfer.NArithTransfer.

Theorem N_nat_ind : forall P : N -> Type, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  Typeclasses eauto := debug.
(*  Fail exactm nat_ind. *)
(*  Fail (transfer; exact nat_ind). *)
  enough (H : Related arrow
                (forall P : nat -> Type, P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n)
                (forall P : N -> Type, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n))
         by (apply H; exact nat_rect).
  apply forall_rule.
  eapply app_rule. {
    eapply subrel_rule; [ refine _ |].
    apply total_predicate.
    refine _.
    Check N2Nat_transfer.inj_iff.
    exact N2Nat_transfer.inj_iff.
  }
  refine _.
Qed.

(*
Set Printing Universes.
Print N_nat_ind.
*)

Theorem ex2 : forall n : nat, n = n.
Proof.
  Fail rewrite <- Nat.pred_succ. (* bizarre *)
  Fail rewrite <- Nat.add_0_l. (* idem *)
  apply nat_ind.
Abort.

Theorem ex3: forall n : N, n = n.
Proof.
  applym nat_ind.
  simpl.
(* Is equivalent to:
  apply N_nat_ind. *)


