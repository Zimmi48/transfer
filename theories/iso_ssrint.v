(* File contributed by Nicolas Magaud *)
(* Cf. "Transferring Arithmetic Decision Procedures (on Z) to Alternative Representations" *)
(* presented at CoqPL 2017 *)

Require Import Transfer.
From Coq Require Import ZArith.
From mathcomp Require Import ssrnum ssrint ssrbool ssrnat ssreflect ssralg.

Open Scope Z_scope.

Definition f (x: int) := match x with Posz t => Z.of_nat t | Negz t => (Zminus (Z.opp (Z.of_nat t)) (1%Z)) end.

Definition R (a:Z) (b:int) := a = f b.

Instance rel1 : forall x : int, Related R (f x) x | 10.
repeat red.
Proof. reflexivity. Qed.

(*
-1 dans Z est représenté par 0 dans int
-2 dans Z est représenté par -1 dans int
-3 dans Z est représenté par -2 dans int
*)

Definition g (x:Z) : int := match x with Z0 => Posz 0%nat | Zpos p => Posz (nat_of_pos p) | Zneg p => Negz( (nat_of_pos p).-1) end.

Lemma of_nat_nat_of_pos : forall p : positive, Z.pos p = Z.of_nat (nat_of_pos p).
Proof.
induction p.
simpl.
rewrite Pos2Z.inj_xI.
rewrite NatTrec.trecE.
rewrite <- addnn.
rewrite Zpos_P_of_succ_nat.
rewrite Nat2Z.inj_add.
rewrite <- IHp.
ring.

simpl.
rewrite Pos2Z.inj_xO.
rewrite NatTrec.trecE.
rewrite <- addnn.
rewrite Nat2Z.inj_add.
rewrite <- IHp.
ring.

simpl; reflexivity.
Qed.

Lemma nat_of_pos_lt_0 : forall p, (0 < nat_of_pos p)%coq_nat.
Proof.
induction p.
simpl.
rewrite NatTrec.trecE.
apply Nat.lt_0_succ.
simpl.
rewrite NatTrec.trecE.
rewrite <- addnn.
replace 0%nat with (0+0)%nat by ring.
apply plus_lt_compat; apply IHp.
simpl.
apply Nat.lt_0_1.
Qed.

Lemma of_nat_nat_of_pos_1 : forall p, Z.of_nat ((nat_of_pos p).-1) = (Z.of_nat (nat_of_pos p))-1.
Proof.
induction p.
simpl nat_of_pos.
rewrite NatTrec.trecE.
rewrite <- addnn.
rewrite Nat2Z.inj_succ.
rewrite Nat2Z.inj_add.
rewrite <- of_nat_nat_of_pos.
ring.

simpl nat_of_pos.
rewrite NatTrec.trecE.
rewrite <- addnn.
rewrite Nat2Z.inj_pred.
rewrite Nat2Z.inj_add.
rewrite <- of_nat_nat_of_pos.
unfold Z.pred; ring.
replace 0%nat with (0+0)%nat by ring.
apply plus_lt_compat; apply nat_of_pos_lt_0.

reflexivity.
Qed.

Instance rel2 : forall x : Z, Related R x (g x) | 10.
Proof.
  unfold Related,R.
  move=> x.
  elim:x.
  reflexivity.
  unfold Related,R; simpl; apply of_nat_nat_of_pos.
  unfold Related,R; simpl.
  intros p.
  rewrite of_nat_nat_of_pos_1.
  rewrite <- of_nat_nat_of_pos.
  ring_simplify; unfold Zopp; reflexivity.
Qed.

Instance Biunique_R : Related (R ##> R ##> iff) (@eq Z) (@eq int).
Proof.
unfold R,f; repeat red.
intros e e'; destruct e'.
intros T e0 e'0; destruct e'0; intros U.
split; intros.
rewrite T U in H.
rewrite <- (Nat2Z.inj n n0 H); reflexivity.
rewrite T U.
apply f_equal.
inversion H; reflexivity.

split; intros.
omega.
inversion H.

intros H e0 e'0; destruct e'0.
split;intros.
omega.
inversion H1.

split; intros.
rewrite H H0 in H1.
apply f_equal; omega.
inversion H1.
rewrite H3 in H.
rewrite H0 H; reflexivity.
Qed.

Instance bitotal_R : Related ((R ##> iff) ##> iff) (@all Z) (@all int).
Proof.
unfold R,all, "##>"; repeat red.
intros e e' o.
split.
intros.
apply -> o.
apply H.
reflexivity.
intros.
apply <- o.
apply (H (g x)).
unfold f,g; destruct x.
simpl; reflexivity.
apply of_nat_nat_of_pos.
rewrite of_nat_nat_of_pos_1.
rewrite <- of_nat_nat_of_pos.
ring_simplify; unfold Zopp; reflexivity.
Qed.

Definition normz (m : int) : int := (absz m)%:Z.

Instance abs_transfer : Related (R ##> R) Z.abs normz.
Proof.
  repeat red; unfold R,f.
  destruct e'; simpl; intros P; inversion P.
  apply Z.abs_eq; apply Nat2Z.is_nonneg.
  rewrite Zpos_P_of_succ_nat.
  unfold Z.succ.
  replace (- Z.of_nat n - 1)%Z with (- (Z.of_nat n + Z.of_nat 1))%Z by (ring).
  replace 1%Z with (Z.of_nat 1) at 1 by reflexivity.
  rewrite <- Nat2Z.inj_add.
  rewrite Z.abs_neq.
  ring.
  rewrite Z.opp_nonpos_nonneg.
  apply Nat2Z.is_nonneg.
Qed.

Lemma N_ok : forall n n0:nat, (n0 < n)%N = false -> (n<=n0)%N.
Proof.
  intros.
  rewrite ltnNge in H.
  apply Bool.negb_false_iff in H.
  by [].
Qed.

Lemma N_ok3 : forall n n0:nat, (n <= n0)%N = true -> (n <= n0)%coq_nat.
Proof.
  repeat red.
  intros.
  generalize (@leP n n0 H); intros F.
  apply F.
Qed.

Lemma N_ok2 : forall n n0:nat, (n < n0)%N = true -> (n < n0)%coq_nat.
Proof.
intros; apply N_ok3; assumption.
Qed.

(*Definition t:  int-> int -> int := @ssralg.GRing.add int_ZmodType.*)

Instance add_transfer : Related (R ##> R ##> R) Z.add intZmod.addz.
Proof.
  unfold R,all,f, "##>"; repeat red.
  intros e e'; destruct e'.
intros T e0 e'0; destruct e'0.
simpl.
intros U; rewrite T U.
rewrite inj_plus; reflexivity.
simpl.
case_eq (n0 <n)%N.
intros P U; rewrite T U.
rewrite Z.add_assoc.
rewrite Nat2Z.inj_sub.
rewrite Nat2Z.inj_succ.
simpl.
unfold Z.succ; ring_simplify.
reflexivity.
apply lt_le_S.
apply N_ok2; assumption.

intros P U; rewrite T U.
assert (P':(n<=n0)%N).
apply N_ok; assumption.

rewrite Z.add_assoc.
rewrite Nat2Z.inj_sub.
ring_simplify; reflexivity.
apply N_ok3; assumption.

destruct e'; simpl.
case_eq (n<n0)%N.
intros P T. rewrite H T.
rewrite Z.add_comm.
rewrite Z.add_assoc.
rewrite Nat2Z.inj_sub.
rewrite Nat2Z.inj_succ.
unfold Zsucc; ring_simplify; reflexivity.
apply lt_le_S.
apply N_ok2; assumption.

intros P U; rewrite H U.
assert (P':(n0<=n)%N).
apply N_ok; assumption.
rewrite Nat2Z.inj_sub.
ring_simplify; reflexivity.
apply N_ok3; assumption.

intros T; rewrite H T.
rewrite <- Pos2Z.opp_pos.
rewrite Z.add_assoc.
replace (- Z.of_nat n - 1 + - Z.of_nat n0 + - (1)) with (- (Z.of_nat n + Z.of_nat n0 + Z.of_nat 2)) by (ring_simplify; reflexivity).
rewrite <- Nat2Z.inj_add.
rewrite Pos2Z.inj_add.
rewrite Zpos_P_of_succ_nat.
ring_simplify; reflexivity.
Qed.

Instance opp_transfer : Related (R ##> R) Z.opp intZmod.oppz.
Proof.
  repeat red; unfold R, f; intros.
  rewrite H.
  case_eq e'; intros; simpl.
  destruct n; simpl.
  reflexivity.
  rewrite <- Pos2Z.opp_pos.
  rewrite Zpos_P_of_succ_nat.
  unfold Z.succ; ring_simplify; reflexivity.
  rewrite Zpos_P_of_succ_nat.
  unfold Z.succ; ring_simplify; reflexivity.
Qed.

Lemma easy : forall x y z:int ,
      z=(intZmod.addz x y) ->
        (match x with | Posz t => Z.of_nat t | Negz t => - Z.of_nat t - 1 end) +
        (match y with | Posz t => Z.of_nat t | Negz t => - Z.of_nat t - 1 end) =
                 match z with | Posz t => Z.of_nat t | Negz t => - Z.of_nat t - 1 end.
Proof.
  intros x y z.
case_eq x; case_eq y; simpl;intros y' Hy x' Hx H.
inversion H.
rewrite Nat2Z.inj_add; reflexivity.
case_eq (y'<x')%N.
intros P; rewrite P in H.
inversion H.
rewrite Nat2Z.inj_sub.
rewrite Nat2Z.inj_succ.
ring_simplify; reflexivity.
apply /leP; assumption.

intros.
rewrite H0 in H.
rewrite H.
ring_simplify.
rewrite Nat2Z.inj_sub.
ring_simplify; reflexivity.
apply /leP; apply N_ok; assumption.

case_eq (x' < y')%N.
intros P; rewrite P in H.
rewrite H.
rewrite Nat2Z.inj_sub.
rewrite Nat2Z.inj_succ.
unfold Zsucc; ring_simplify; reflexivity.
apply /leP; assumption.
intros P; rewrite P in H.
rewrite H.
rewrite Nat2Z.inj_sub.
ring_simplify; reflexivity.
apply /leP; apply N_ok; assumption.

rewrite H.
rewrite Nat2Z.inj_succ.
rewrite Nat2Z.inj_add.
unfold Z.succ; ring_simplify; reflexivity.
Qed.

Instance mul_transfer : Related (R ##> R ##> R) Z.mul intRing.mulz.
Proof.
repeat red; unfold R; intros e e' He e0 e'0 He0; rewrite He He0; clear He He0 e e0; unfold f.
induction e'0.
intros; rewrite intRing.mulz0; simpl in *; ring.
rewrite intRing.mulzS.
simpl.
rewrite Zpos_P_of_succ_nat.
rewrite <- Zmult_succ_r_reverse.
rewrite IHe'0.
apply easy.
rewrite intZmod.addzC.
reflexivity.

simpl.
rewrite <- intZmod.NegzE.

case_eq e'; simpl.
simpl; intros.
case_eq n0; case_eq n; simpl.
reflexivity.
reflexivity.
intros.
rewrite <- Pos2Z.opp_pos.
rewrite Pos.mul_1_r.
unfold muln_rec; rewrite Nat.mul_1_r.
rewrite Zpos_P_of_succ_nat.
unfold Zsucc; ring_simplify; reflexivity.

intros.
rewrite <- Pos2Z.opp_pos.
rewrite <- Pos2Z.opp_pos.
replace 1%positive with (Pos.of_nat 1)%nat by reflexivity.
apply f_equal.
apply f_equal.

rewrite Pos.of_nat_succ.
rewrite Pos.of_nat_succ.
rewrite Pos.of_nat_succ.
rewrite <- Nat2Pos.inj_add by (intro T; inversion T).
rewrite <- Nat2Pos.inj_mul by (intro T; inversion T).
rewrite <- Nat2Pos.inj_add by (intro T; inversion T).
apply f_equal.
replace (n1.+2)%nat with (n1.+1 + 1)%nat by (ring_simplify; reflexivity).
ring_simplify; unfold muln_rec,addn, addn_rec; simpl.
repeat rewrite <- Nat.add_assoc; rewrite (Nat.add_comm 1); reflexivity.

(*
case_eq n2.
rewrite Nat.mul_1_l.
intros.
unfold muln_rec; rewrite Nat.mul_0_l.
rewrite <- plus_n_O.
rewrite <- Nat2Pos.inj_add by (intro T; inversion T).
reflexivity.
intros.
rewrite Nat2Pos.inj_succ.
rewrite Pos.add_succ_l.

Check Nat2Pos.inj_succ.
(*rewrite Nat2Pos.inj_succ.*)
apply f_equal.
apply f_equal.
(*rewrite Nat2Pos.inj_succ.*)
rewrite <- Nat2Pos.inj_add.

repeat rewrite <- Nat.add_assoc; ; reflexivity.
apply ft.
apply fu.
intro T; inversion T.
apply fu.
*)
(* *)
intros.
rewrite Zpos_P_of_succ_nat.
unfold Zsucc.
ring_simplify.
rewrite <- inj_mult.
rewrite <- inj_plus.
rewrite <- inj_plus.
apply f_equal with (f:=fun x => x+1).
apply f_equal.
unfold muln_rec.
rewrite Nat.mul_succ_r.
rewrite Nat.add_comm.
reflexivity.
Qed.

Check Num.Def.ler.
Check (rel int).
Definition ler' : int -> int -> Prop := Num.Def.ler.

Instance le_transfer : Related (R ##> R ##> iff) Z.le ler'.
repeat red; unfold R, f, ler', Num.le.
intros.
destruct e'; destruct e'0; simpl; split; intros; subst.
rewrite <- Nat2Z.inj_le in H1.
apply /leP; assumption.
rewrite <- Nat2Z.inj_le.
apply /leP; assumption.
omega.
by [].
by [].
omega.
apply /leP; omega.
apply Z.le_sub_le_add.
rewrite Z.add_comm.
apply Z.add_le_mono_l.
rewrite <- Z.opp_le_mono.
rewrite <- Nat2Z.inj_le.
apply /leP; assumption.
Qed.

Definition ltr' : int -> int -> Prop := Num.Def.ltr.

(*
Print Scopes.

Scope ring_scope
No delimiting key
Bound to classes int Num.RealField.sort Num.RealDomain.sort Num.RealClosedField.sort
Num.NumField.sort Num.NumDomain.sort Num.ClosedField.sort Num.ArchimedeanField.sort
"`| x |" := Num.Def.normr x
"x ^ n" := exprz x n
"x >= y :> T" := Num.Def.ler (y : T) (x : T)
"x >= y" := Num.Def.ler y x
"x > y :> T" := Num.Def.ltr (y : T) (x : T)
"x > y" := Num.Def.ltr y x
"n == m :> 'in' 't'" := eqtype.eq_op n m
"n = m :> 'in' 't'" := eq n m
"n <> m :> 'in' 't'" := not (eq n m)
"x <= y ?= 'iff' C :> R" := Num.Def.lerif (x : R) (y : R) C
"x <= y ?= 'iff' C" := Num.Def.lerif x y C
"x <= y <= z" := andb (Num.Def.ler x y) (Num.Def.ler y z)
"x <= y < z" := andb (Num.Def.ler x y) (Num.Def.ltr y z)
"x <= y :> T" := Num.Def.ler (x : T) (y : T)
"x <= y" := Num.Def.ler x y
"x < y <= z" := andb (Num.Def.ltr x y) (Num.Def.ler y z)
"x < y < z" := andb (Num.Def.ltr x y) (Num.Def.ltr y z)
"x < y :> T" := Num.Def.ltr (x : T) (y : T)
"x < y" := Num.Def.ltr x y
"x *~ n" := intmul x n
"n %:~R" := intmul (ssralg.GRing.one _) n
"n %:Z" := Posz n
"n != m :> 'in' 't'" := negb (eqtype.eq_op n m)
">=%R" := Num.Def.ger
">= y :> T" := Num.Def.ler (y : T)
">= y" := Num.Def.ler y
">%R" := Num.Def.gtr
"> y :> T" := Num.Def.ltr (y : T)
"> y" := Num.Def.ltr y
"<?=%R" := Num.Def.lerif
"<=%R" := Num.Def.ler
"<= y :> T" := Num.Def.ger (y : T)
"<= y" := Num.Def.ger y
"<%R" := Num.Def.ltr
"< y :> T" := Num.Def.gtr (y : T)
"< y" := Num.Def.gtr y
"*~%R" := intmul (R:=_)
*)

Instance lt_transfer : Related (R ##> R ##> iff) Z.lt ltr'.
Proof.
repeat red; unfold R, f, ltr', Num.lt.
intros.
destruct e'; destruct e'0; simpl; split; intros; subst.
rewrite <- Nat2Z.inj_lt in H1.
apply /leP; assumption.
rewrite <- Nat2Z.inj_lt.
apply /leP; assumption.
omega.
by [].
by [].
omega.
apply /leP; omega.
apply Z.lt_sub_lt_add.
rewrite Z.add_comm.
apply Z.add_lt_mono_l.
rewrite <- Z.opp_lt_mono.
rewrite <- Nat2Z.inj_lt.
apply /ltP; assumption.
Qed.

Definition gtr' ( x y : int) : Prop :=  Num.gt x y.

Instance gt_transfer : Related (R ##> R ##> iff) Z.gt gtr'.
Proof.
  unfold gtr'; repeat red; intros.
  rewrite Num.Theory.gtrE; rewrite Z.gt_lt_iff.
  apply lt_transfer; assumption.
Qed.

Definition ger' (x y : int) : Prop := Num.ge x y.

Instance ge_transfer : Related (R ##> R ##> iff) Z.ge ger'.
Proof.
  unfold ger'; repeat red; intros.
  rewrite Num.Theory.gerE; rewrite Z.ge_le_iff.
  apply le_transfer; assumption.
Qed.
