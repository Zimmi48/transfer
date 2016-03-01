(** This file is a tentative translation of SetNat.thy by Daniel Raggi et al.
    See http://homepages.inf.ed.ac.uk/s1052074/AutoTransfer/ for the original
    Isabelle file.
*)

Require Import MSets.
Require Import Transfer.
Require Import Omega.

(** Because MSets are generic, we give generic transfer declarations.
    Because some transfer properties require it, we will ask that
    element type is infinite. *)

Module Type IsInfinite (Import T:Equalities.DecidableType).

  Parameter (infty : nat -> t).
  Parameter (infty_inj : forall n p, eq (infty n) (infty p) -> n = p).

End IsInfinite.

Module Type InfDecType <: DecidableType :=
  Equalities.DecidableType <+ IsInfinite.

Module TransferProp (E:InfDecType)(Fin:WSetsOn E).

  Module FinProp := WPropertiesOn E Fin.
  Module FinDec := WDecideOn E Fin.

  (** Sets are related to their cardinal *)

  Definition SetNat s n := Fin.cardinal s = n.

  (** 0 has a unique and canonical set representation *)
  Instance empty_0 : Related SetNat Fin.empty 0 := FinProp.empty_cardinal.

  Instance singleton_1 : forall x, Related SetNat (Fin.singleton x) 1.
  Proof. apply FinProp.singleton_cardinal. Qed.

  Fixpoint ordinal n :=
    match n with
    | 0 => Fin.empty
    | S n => Fin.add (E.infty n) (ordinal n)
    end.

  Lemma ordinal_cardinal : forall n, Fin.cardinal (ordinal n) = n.
  Proof.
    enough (
      forall n, Fin.cardinal (ordinal n) = n /\
      forall m, Fin.In (E.infty m) (ordinal n) -> m < n
    ) by firstorder.
    induction n.
    + split.
      - exact FinProp.empty_cardinal.
      - FinDec.fsetdec.
    + split.
      - cbn.
        destruct IHn as [Hcard Hmax].
        rewrite <- Hcard at 3.
        apply FinProp.add_cardinal_2.
        firstorder omega.
      - cbn.
        intros m H.
        apply Fin.add_spec in H.
        destruct H as [H|H].
        * apply E.infty_inj in H.
          omega.
        * firstorder omega.
  Qed.

  Instance ordinal_n : forall n, Related SetNat (ordinal n) n | 9.
  Proof. apply ordinal_cardinal. Qed.

  Instance anyset_cardinal : forall s, Related SetNat s (Fin.cardinal s).
  Proof. reflexivity. Qed.

  (* Missing definition of cartesian product on MSets *)

  Ltac SetNat_basics :=
    related_basics;
    unfold SetNat;
    repeat (
      let x1 := fresh "s" in
      let x2 := fresh "s" in
      let Hx := fresh "Hs" in
      intros x1 x2 Hx;
      rewrite <- Hx;
      clear Hx x2 ).

  Instance subset_le : Related (SetNat ##> SetNat ##> impl) Fin.Subset le.
  Proof.
    SetNat_basics.
    apply FinProp.subset_cardinal.
  Qed.

  (** Adding a missing definition of strict subset *)
  Definition StrictSubset s1 s2 :=
    Fin.Subset s1 s2 /\ exists x, Fin.In x s2 /\ ~ Fin.In x s1.

  Instance strictsubset_lt :
    Related (SetNat ##> SetNat ##> impl) StrictSubset lt.
  Proof.
    SetNat_basics.
    unfold StrictSubset.
    intros [Hsub [x [Hin2 Hnotin1]]].
    eapply FinProp.subset_cardinal_lt; eauto.
  Qed.

  Instance injectivity : Related (SetNat ##> SetNat ##> impl) Fin.eq Logic.eq.
  Proof.
    SetNat_basics.
    intros Heq.
    rewrite Heq.
    reflexivity.
  Qed.

  Instance surjectivity : Related ((SetNat ##> impl) ##> impl) (@all _) (@all _).
  Proof.
    apply surj_decl.
    intros n.
    exists (ordinal n).
    apply ordinal_cardinal.
  Qed.

  Instance totality : Related ((SetNat ##> flip impl) ##> flip impl) (@all _) (@all _).
  Proof.
    apply tot_decl.
    intros x.
    exists (Fin.cardinal x).
    reflexivity.
  Qed.

  Definition addNew_pred (x : Fin.elt) (s1 : Fin.t) (s2 : Fin.t) :=
    ~ Fin.In x s1 /\ FinProp.Add x s1 s2.
  Definition succ_pred x y := S x = y.

  Instance addNew_succ :
    forall x, Related (SetNat ##> SetNat ##> impl) (addNew_pred x) succ_pred.
  Proof.
    SetNat_basics.
    unfold addNew_pred.
    unfold succ_pred.
    intros [H1 H2].
    symmetry.
    exact (FinProp.cardinal_2 H1 H2).
  Qed.

  (** Exactly as for Isabelle transfer package, we cannot express
      the following lemma as a transfer rule. *)
  Lemma disj_union :
    forall s1 n1, SetNat s1 n1 ->
    forall s2 n2, SetNat s2 n2 ->
    Fin.Empty (Fin.inter s1 s2) ->
    SetNat (Fin.union s1 s2) (n1 + n2).
  Proof.
    unfold SetNat.
    intros s1 n1 H1 s2 n2 H2 Hcond.
    assert (Hinter0 : Fin.cardinal (Fin.inter s1 s2) = 0)
      by now apply FinProp.cardinal_Empty.
    rewrite <- H1, <- H2.
    rewrite <- FinProp.union_inter_cardinal.
    rewrite Hinter0.
    apply plus_n_O.
  Qed.

  (** There is a solution with partial functions but how can we
      make use of it? *)
  Definition disjSum s1 s2 :=
    if Fin.is_empty (Fin.inter s1 s2) then Some (Fin.union s1 s2) else None.

  Inductive SetOptionNat : option Fin.t -> nat -> Prop :=
  | someSet : forall s n, SetNat s n -> SetOptionNat (Some s) n
  | noSet : forall n, SetOptionNat None n.

  Instance toSetOptionNat :
    Related (SetNat ##> SetOptionNat) (@Some Fin.t) id.
  Proof.
    SetNat_basics.
    apply someSet.
    reflexivity.
  Qed.

  Instance disj_union_bis :
    Related (SetNat ##> SetNat ##> SetOptionNat) disjSum Nat.add.
  Proof.
    SetNat_basics.
    unfold disjSum.
    destruct (Fin.is_empty (Fin.inter s s0)) eqn:Hempty.
    + apply someSet.
      unfold SetNat.
      assert (Hinter0 : Fin.cardinal (Fin.inter s s0) = 0). {
        apply Fin.is_empty_spec in Hempty.
        now apply FinProp.cardinal_Empty.
      }
      rewrite plus_n_O at 1.
      rewrite <- Hinter0.
      apply FinProp.union_inter_cardinal.
    + apply noSet.
  Qed.

  Definition disjSum_pred s1 s2 s3 :=
    Fin.Empty (Fin.inter s1 s2) /\ Fin.Equal (Fin.union s1 s2) s3.
  
  Definition sum_pred n1 n2 n3 := n1 + n2 = n3.
  
  Instance disj_union_ter :
    Related (SetNat ##> SetNat ##> SetNat ##> impl) disjSum_pred sum_pred.
  Proof.
    SetNat_basics.
    unfold disjSum_pred.
    unfold sum_pred.
    intros [H1 H2].
    rewrite <- H2.
    symmetry.
    apply disj_union; trivial.
    all:reflexivity.
  Qed.

  (* Tests *)

  Goal 0 + 1 = 1.
  Proof.
    enough (disjSum_pred Fin.empty (Fin.singleton (E.infty 0))
                         (Fin.singleton (E.infty 0))). {
      change (sum_pred 0 1 1).
      exactm H.
    }
    unfold disjSum_pred.
    split; FinDec.fsetdec.
  Qed.

  (* This is still a little too much complicated!
     And we do not have a choose operator to try more interesting proofs. *)

End TransferProp.