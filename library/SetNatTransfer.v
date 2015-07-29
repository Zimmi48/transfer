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
  Instance empty_0 : Related SetNat Fin.empty 0.
  Proof.
    split.
    exact FinProp.empty_cardinal.
  Qed.

  Instance singleton_1 : forall x, Related SetNat (Fin.singleton x) 1.
  Proof.
    split.
    apply FinProp.singleton_cardinal.
  Qed.

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
        intros m [H|H]/Fin.add_spec.
        * apply E.infty_inj in H.
          omega.
        * firstorder omega.
  Qed.

  Instance ordinal_n : forall n, Related SetNat (ordinal n) n.
  Proof.
    split.
    apply ordinal_cardinal.
  Qed.

  Instance anyset_cardinal : forall s, Related SetNat s (Fin.cardinal s).
  Proof.
    split.
    reflexivity.
  Qed.

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
    split.
    apply surj_decl.
    intros n.
    exists (ordinal n).
    apply ordinal_cardinal.
  Qed.

  Instance totality : Related ((SetNat ##> flip impl) ##> flip impl) (@all _) (@all _).
  Proof.
    split.
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

  Typeclasses eauto := debug.

  Goal 0 + 1 = 1.
  Proof.
    apply modulo.
    reflexivity.
    Unshelve.
    exact (E.infty 0).
  Qed.

  Goal forall x, S x = x + 1.
  Proof.
    Fail apply modulo.
  Abort.

End TransferProp.