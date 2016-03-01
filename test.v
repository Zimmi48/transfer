Require Import PeanoNat.
Require Import NArithTransfer.

Lemma half_total_predicate :
  forall {A B : Type} (R : A -> B -> Prop),
    (forall (x : A) (x' y' : B), R x x' -> R x y' -> x' = y')
    -> forall P' : B -> Prop, exists P : A -> Prop, (R ##> iff) P P'.
Proof.
  intros A B R Hfun P'.
  exists (fun x => forall x', R x x' -> P' x').
(*  exists (fun x => exists x', R x x' /\ P' x'). *)
  intros; split; firstorder.
  erewrite Hfun; eauto.
Qed.  

Lemma half_total_predicate_recip :
  forall (A B : Type) (R : A -> B -> Prop),
    (forall P' : B -> Prop, exists P : A -> Prop, (R ##> iff) P P') ->
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
    (forall x', exists x, R x x') ->
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
  (Related ((R ##> iff) ##> iff) (@all A) (@all B)) ->
  Related ((R ##> iff) ##> (R ##> iff) ##> iff) (eq ##> iff) (eq ##> iff).
Proof.
  intro.
  destruct (full_tot_decl_recip _ _ _ is_related) as [ Hsurj Htot ].
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
  Related (((R ##> iff) ##> iff) ##> iff) (@all (A -> Prop)) (@all (B -> Prop)).
Proof.
  destruct (full_uniq_decl_recip _ _ _ is_related) as [ Hfun Hinj ].
  apply full_tot_decl; split.
  + exact (half_total_predicate _ Hfun).
  + intros *.
    edestruct (half_total_predicate (flip R)) as (P' & HP'); [ intros; eapply Hinj; eauto |].
    exists P'.
    intros; split; apply HP'; assumption.
Qed.

Theorem N_nat_ind : forall P : N -> Prop, P 0%N -> (forall n : N, P n -> P (N.succ n)) -> forall n : N, P n.
Proof.
  transfer.
  exact nat_ind.
(*   exactm nat_ind. *)
Qed.

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


