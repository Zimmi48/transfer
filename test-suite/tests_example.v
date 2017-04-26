(* File contributed by Nicolas Magaud *)
(* Cf. "Transferring Arithmetic Decision Procedures (on Z) to Alternative Representations" *)
(* presented at CoqPL 2017 *)

From mathcomp Require Import ssrint ssrnum ssrbool.
From Coq Require Import ZArith Psatz.
Require Import Transfer tactics iso_ssrint.

(* false in Q : x=1/2 and n=1 *)

Lemma not_so_easy : forall x n : Z,
    2*x + 1 <= 2 *n -> x <= n-1.
Proof.
  intros;lia.
Qed.

Open Scope int_scope.

Notation "x + y" := (intZmod.addz x y) : int_scope.
Notation "x - y" := (x + intZmod.oppz y) : int_scope.
Notation "x * y" := (intRing.mulz x y) : int_scope.

Notation "- y" := (intZmod.oppz y) : int_scope.

Notation "x <= y" := (ler' x y) : int_scope.
Notation "x >= y" := (ger' x y) : int_scope.
Notation "x > y" := (gtr' x y) : int_scope.
Notation "x < y" := (ltr' x y) : int_scope.

Notation "0" := 0%:Z : int_scope.
Notation "1" := 1%:Z : int_scope.
Notation "2" := 2%:Z : int_scope.
Notation "3" := 3%:Z : int_scope.
Notation "4" := 4%:Z : int_scope.
Notation "7" := 7%:Z : int_scope.
Notation "12" := 12%:Z : int_scope.
(*
Instance r0 : Related R 0%Z 0%:Z.
Proof. reflexivity. Qed.

Instance r1 : Related R 1%Z 1%:Z.
Proof. reflexivity. Qed.

Instance r2 : Related R 2%Z 2%:Z.
Proof. reflexivity. Qed.

Instance r3 : Related R 3%Z 3%:Z.
Proof. reflexivity. Qed.

Instance r4 : Related R 4%Z 4%:Z.
Proof. reflexivity. Qed.

Instance r7 : Related R 7%Z 7%:Z.
Proof. reflexivity. Qed.

Instance r12 : Related R 12%Z 12%:Z.
Proof. reflexivity. Qed.
*)
Lemma easy2 : forall x y:int,
    match ssralg.GRing.mul (R:=ssralg.GRing.UnitRing.ringType int_unitRingType) x y with
    | Posz t => Z.of_nat t
    | Negz t => (- Z.of_nat t - 1)%Z     end =
    Z.mul (match x with
           | Posz t => Z.of_nat t
           | Negz t => (- Z.of_nat t - 1)%Z end)
          (match  y with
           | Posz t => Z.of_nat t
           | Negz t => (- Z.of_nat t - 1)%Z end).
Proof.
  intros.
  destruct x; destruct y; unfold ssralg.GRing.mul; simpl.
  unfold ssrnat.muln, ssrnat.muln_rec.
  rewrite Nat2Z.inj_mul; reflexivity.
  case_eq n.
  simpl;reflexivity.
  intros.
  rewrite ssrnat.mulnS.
  rewrite ssrnat.addSn.
  rewrite <- NegzE.
  unfold  ssrnat.addn, ssrnat.addn_rec, ssrnat.muln, ssrnat.muln_rec.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_succ.
  ring_simplify; reflexivity.

  case_eq n0.
  intros; simpl; ring_simplify;reflexivity.
  intros.
  rewrite ssrnat.mulnS.
  rewrite ssrnat.addSn.
  rewrite <- NegzE.
  unfold  ssrnat.addn, ssrnat.addn_rec, ssrnat.muln, ssrnat.muln_rec.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_succ.
  ring_simplify; reflexivity.

  unfold  ssrnat.addn, ssrnat.addn_rec, ssrnat.muln, ssrnat.muln_rec.
  rewrite Zpos_P_of_succ_nat.
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Nat2Z.inj_succ.
  ring_simplify; reflexivity.
Qed.

Definition Zpow' (x : Z) (n:nat) : Z := (Z.pow x (Z.of_nat n))%Z.
Definition exprz' : int -> nat -> int := (@exprz int_unitRingType).

Lemma exprz_lemma : exprz 2 (Negz 2%nat) = 8%:Z.
Proof.
  compute; reflexivity.
Qed.

Lemma Zpow_lemma : (Z.pow 2 (-3) = 0)%Z.
Proof.
   compute; reflexivity.
Qed.

Definition Rnat ( x y:nat):= x=y.

Instance pow_transfer : Related (R ##> Rnat ##> R) Zpow' exprz'.
Proof.
  repeat red; unfold R,f; unfold Zpow', exprz',Rnat; intros.
  revert H0 H; revert e e' e0; induction e'0.
  intros.
  inversion H0.
  rewrite <- exprnP.
  simpl; reflexivity.
  intros.
  rewrite exprSz.
  generalize (IHe'0 e e' e'0 (eq_refl e'0) H).
  intros.
  rewrite easy2.
  rewrite <- H1.
  rewrite <- H.
  rewrite H0.
  rewrite <- Zpower_nat_Z.
  rewrite <- Zpower_nat_Z.
  rewrite Zpower_nat_succ_r.
  reflexivity.
Qed.

Lemma exponent2_Z : (Z.of_nat 2 = Zpos (xO xH))%Z.
Proof.
  compute; reflexivity.
Qed.

Lemma exponent3_Z : Z.of_nat 3 = Zpos (xI xH).
Proof.
  compute; reflexivity.
Qed.

Lemma exponent4_Z : Z.of_nat 4 = Zpos (xO (xO xH)).
Proof.
  compute; reflexivity.
Qed.

Ltac wrap2 := match goal with | [|- forall  x:_, _] => intro x ; unfold Zpow'; repeat (rewrite exponent2_Z|| rewrite exponent3_Z || rewrite exponent4_Z); wrap2; revert x| _ => idtac end.

Ltac wtransfer' := wtransfer; wrap2.

Notation "x ^ n" := (exprz' x n) : ring_scope.
Notation "x ^ n" := (exprz' x n) : int_scope.

Lemma not_so_easy' :  forall x n : int,  2*x + 1 <= 2 *n ->  x <= n-1.
Proof.
  tlia.
Qed.

(* From Laurent Théry *)

Lemma some_pol' : forall x:int, 4 * x ^ 2 + 3 * x + 2 >= 0.
Proof.
  wtransfer'.
  intros; psatz Z 2.
Qed.

Lemma Zdiscr: forall a b c x : int,
  a * x ^ 2 + b * x + c = 0 -> b ^ 2  - 4 * a * c >= 0.
Proof.
  wtransfer'.
  intros ; psatz Z 4.
Qed.


Lemma plus_minus : forall x y,
  0 = x + y -> 0 =  x -y -> 0 = x /\ 0 = y.
Proof.
  tlia.
Qed.

Lemma mplus_minus : forall x y,
  x + y >= 0 -> x -y >= 0 -> x^2 - y^2 >= 0.
Proof.
  wtransfer'.
  intros; psatz Z 2.
Qed.

Lemma pol3: forall x y, 0 <= x + y ->
  x^3 + 3*x^2*y + 3*x* y^2 + y^3 >= 0.
Proof.
  wtransfer'.
  intros; psatz Z 4.
Qed.

(* Motivating example from: Expressiveness + Automation + Soundness:
   Towards COmbining SMT Solvers and Interactive Proof Assistants *)
Section example.

Variable rho' : Z.
Variable rho_ge' : (rho' >= 0)%Z.
Variable correct' : Z -> Z -> Prop.


Definition rbound1' (C:Z -> Z -> Z) : Prop :=
  forall p s t, (correct' p t /\ s <= t -> C p t - C p s <= (1-rho')*(t-s))%Z.

Definition rbound2' (C:Z -> Z -> Z) : Prop :=
  forall p s t, (correct' p t /\ s <= t ->  (1-rho')*(t-s) <= C p t - C p s)%Z.


Lemma bounded_drift' : forall s t p q C D, (s <= t /\ correct' p t  /\ correct' q t /\
  rbound1' C /\ rbound2' C /\ rbound1' D /\ rbound2' D  ->
  Z.abs (C p t - D q t) <= Z.abs (C p s - D q s) + 2 * rho' * (t- s))%Z.
Proof.
  intros.
  generalize (Z.abs_eq (C p t - D q t)).
  generalize (Z.abs_neq (C p t - D q t)).
  generalize (Z.abs_eq (C p s -D q s)).
  generalize (Z.abs_neq (C p s - D q s)).
  unfold rbound2' in H.
  unfold rbound1' in H.
  intuition.
  generalize (H6 _ _ _ (conj H H4)).
  generalize (H7 _ _ _ (conj H H4)).
  generalize (H8 _ _ _ (conj H H4)).
  generalize (H10 _ _ _ (conj H H4)).
  generalize (H6 _ _ _ (conj H5 H4)).
  generalize (H7 _ _ _ (conj H5 H4)).
  generalize (H8 _ _ _ (conj H5 H4)).
  generalize (H10 _ _ _ (conj H5 H4)).
  generalize rho_ge'.
  psatz Z 2.
Qed.

End example.

(*
(* Motivating example from: Expressiveness + Automation + Soundness:
   Towards COmbining SMT Solvers and Interactive Proof Assistants *)
Section example2.

Variable rho : int.
Variable rho_ge : rho >= 0.
Variable correct : int -> int -> Prop.


Definition rbound1 (C:int -> int -> int) : Prop :=
  forall p s t, correct p t /\ s <= t -> C p t - C p s <= (1-rho)*(t-s).

Definition rbound2 (C:int -> int -> int) : Prop :=
  forall p s t, correct p t /\ s <= t ->  (1-rho)*(t-s) <= C p t - C p s.

Variable s t p q:int.
Variable C D : int -> int -> int.

Variable C' D': Z-> Z -> Z.
Variable correct' : Z->Z->Prop.
Variable rho' : Z.

Instance rr : Related R rho' rho.
Admitted.

Instance rC : Related (R ##> R ##> R) C' C.
Admitted.

Instance rD : Related (R ##> R ##> R) D' D.
Admitted.

Instance rcorrect : Related (R ##> R ##> iff) correct' correct.
Admitted.

Lemma bounded_drift : (*forall s t p q C D,*) s <= t /\ correct p t  /\ correct q t /\
  rbound1 C /\ rbound2 C /\ rbound1 D /\ rbound2 D  ->
  normz (C p t - D q t) <= normz (C p s - D q s) + 2 * rho * (t- s).
Proof.
  intros.
(*  generalize (@gez0_abs (C p t - D q t)).*)
  generalize ((@gez0_abs (C p t - D q t)):(0 <= (C p t - D q t)) -> (normz (C p t + - D q t) = (C p t - D q t))).
  (*  generalize (@lez0_abs (C p t - D q t)).*)
    generalize ((@lez0_abs (C p t - D q t)):((C p t - D q t) <= 0 -> (normz (C p t + - D q t) = - (C p t - D q t)))).
(*    generalize (@gez0_abs (C p s -D q s)).*)
      generalize ((@gez0_abs (C p s -D q s)):(0 <= (C p s - D q s) -> (normz (C p s + - D q s) = C p s - D q s))).
(*      generalize (@lez0_abs (C p s - D q s)).*)
        generalize ((@lez0_abs (C p s - D q s)): ((C p s - D q s) <= 0 -> (normz (C p s + - D q s) = - (C p s - D q s)))).
  unfold rbound2 in H.
  unfold rbound1 in H.
  intuition.
  generalize (H6 _ _ _ (conj H H4)).
  generalize (H7 _ _ _ (conj H H4)).
  generalize (H8 _ _ _ (conj H H4)).
  generalize (H10 _ _ _ (conj H H4)).
  generalize (H6 _ _ _ (conj H5 H4)).
  generalize (H7 _ _ _ (conj H5 H4)).
  generalize (H8 _ _ _ (conj H5 H4)).
  generalize (H10 _ _ _ (conj H5 H4)).
  generalize rho_ge.
  revert H10 H8 H7 H6 H5 H H4 H3 H2 H1 H0.  revert C D s t p q correct rho_ge.  revert rho.

  transfer.
  intros; eapply bounded_drift' with (correct':=correct).

  psatz Z 2.
Qed.

End additionnal_hyps.
*)

(* Rule of signs *)

Lemma sign_pos_pos: forall x y:int,
  x > 0 -> y > 0 -> x*y > 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_pos_zero: forall x y,
  x > 0 -> y = 0 -> x*y = 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_pos_neg: forall x y,
  x > 0 -> y < 0 -> x*y < 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_zer_pos: forall x y,
  x = 0 -> y > 0 -> x*y = 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_zero_zero: forall x y,
  x = 0 -> y = 0 -> x*y = 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_zero_neg: forall x y,
  x = 0 -> y < 0 -> x*y = 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_neg_pos: forall x y,
  x < 0 -> y > 0 -> x*y < 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_neg_zero: forall x y,
  x < 0 -> y = 0 -> x*y = 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.

Lemma sign_neg_neg: forall x y,
  x < 0 -> y < 0 -> x*y > 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.


(* Other (simple) examples *)

Lemma binomial : forall x y, (x+y)^2 = x^2 + 2*x*y + y^2.
Proof.
  wtransfer'.
  intros; lia.
Qed.

Lemma product : forall x y, x >= 0 -> y >= 0 -> x * y >= 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.


Lemma product_strict : forall x y, x > 0 -> y > 0 -> x * y > 0.
Proof.
  transfer.
  simpl (f _).
  intros; psatz Z 2.
Qed.


Lemma pow_2_pos : forall x:int, x ^ 2 + 1 = 0 ->  False.
Proof.
  wtransfer'.
  intros ; psatz Z 2.
Qed.

(* Found in Parrilo's talk *)
(* BUG?: certificate with **very** big coefficients *)
Lemma parrilo_ex : forall x y : int, x - y^2 + 3 >= 0 -> y + x^2 + 2 = 0 -> False.
Proof.
  wtransfer'.
  intros; psatz Z 2.
Qed.

(* from hol_light/Examples/sos.ml *)

Lemma hol_light1 : forall a1 a2 b1 b2,
  a1 >= 0 -> a2 >= 0 ->
   (a1 * a1 + a2 * a2 = b1 * b1 + b2 * b2 + 2) ->
   (a1 * b1 + a2 * b2 = 0) -> a1 * a2 - b1 * b2 >= 0.
Proof.
  transfer.
  simpl (f _).
  intros ; psatz Z 4.
Qed.


Lemma hol_light2 : forall x a,
        3 * x + 7 * a < 4 -> 3 < 2 * x -> a < 0.
Proof.
  transfer.
  simpl (f _).
  intros ; psatz Z 2.
Qed.

Lemma hol_light3 : forall b a c x:int,
  b ^ 2 < 4 * a * c -> (a * x ^2  + b * x + c = 0) -> False.
Proof.
  wtransfer'.
  intros ; psatz Z 4.
Qed.

Lemma hol_light4 : forall a c b x:int,
  a * x ^ 2 + b * x + c = 0 -> b ^ 2 >= 4 * a * c.
Proof.
  wtransfer'.
  intros ; psatz Z 4.
Qed.

Lemma hol_light5 : forall x y,
    0 <= x /\ x <= 1 /\ 0 <= y /\ y <= 1
     -> x ^ 2 + y ^ 2 < 1 \/
      (x - 1) ^ 2 + y ^ 2 < 1 \/
      x ^ 2 + (y - 1) ^ 2 < 1 \/
      (x - 1) ^ 2 + (y - 1) ^ 2 < 1.
Proof.
  wtransfer'.
  intros; psatz Z 3.
Qed.



Lemma hol_light7 : forall x y z,
 0<= x /\ 0 <= y /\ 0 <= z /\ x + y + z <= 3
  -> x * y + x * z + y * z >= 3 * x * y * z.
Proof.
  transfer.
  simpl (f _).
  intros ; psatz Z 3.
Qed.

Lemma hol_light8 : forall x y z:int,
 x ^ 2 + y ^ 2 + z ^ 2 = 1 -> (x + y + z) ^ 2 <= 3.
Proof.
  wtransfer'.
  intros ; psatz Z 2.
Qed.

Lemma hol_light9 : forall w x y z:int,
 w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 = 1
  -> (w + x + y + z) ^ 2 <= 4.
Proof.
  wtransfer'.
  intros; psatz Z 2.
Qed.

Lemma hol_light10 : forall x y,
 x >= 1 /\ y >= 1 -> x * y >= x + y - 1.
Proof.
  wtransfer'.
  intros ; psatz Z 2.
Qed.

Lemma hol_light11 : forall x y,
 x > 1 /\ y > 1 -> x * y > x + y - 1.
Proof.
  transfer.
  simpl (f _).
  intros ; psatz Z 2.
Qed.

Lemma hol_light12: forall x y z:Z,
 ( 2 <= x /\ x <= 125841 / 50000 /\
  2 <= y /\ y <= 125841 / 50000 /\
  2 <= z /\ z <= 125841 / 50000
   -> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) >= 0)%Z.
Proof.
  intros x y z.
  set (e:= (125841 / 50000)).
  compute in e.
  unfold e ; intros ; psatz Z 2.
Qed.

(*
  (* TODO find Zdiv in ssrint : Num.Theory.divr_ge0. *)
Lemma hol_light12: forall x y z,
  2 <= x /\ x <= 125841 / 50000 /\
  2 <= y /\ y <= 125841 / 50000 /\
  2 <= z /\ z <= 125841 / 50000
   -> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) >= 0.
Proof.
  intros x y z ; set (e:= (125841 / 50000)).
  compute in e.
  unfold e ; intros ; psatz Z 2.
Qed.
*)

Lemma hol_light12_bis: forall x y z:int,
  2 <= x /\ x <= 2 /\
  2 <= y /\ y <= 2 /\
  2 <= z /\ z <= 2
   -> 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z) >= 0.
Proof.
  transfer.
  simpl (f _).
  intros x y z.
  (*unfold e ;*) intros ; psatz Z 2.
Qed.

Lemma hol_light14 : forall x y z,
 2 <= x /\ x <= 4 /\ 2 <= y /\ y <= 4 /\ 2 <= z /\ z <= 4
  -> 12 <= 2 * (x * z + x * y + y * z) - (x * x + y * y + z * z).
Proof.
  transfer.
  simpl (f _).
  intros ;psatz Z 2.
Qed.

(* ------------------------------------------------------------------------- *)
(* Inequality from sci.math (see "Leon-Sotelo, por favor").                  *)
(* ------------------------------------------------------------------------- *)

Lemma hol_light16 : forall x y,
  0 <= x /\ 0 <= y /\ (x * y = 1)
   -> x + y <= x ^ 2 + y ^ 2.
Proof.
  wtransfer'.
  intros ; psatz Z 2.
Qed.

Lemma hol_light17 : forall x y,
  0 <= x /\ 0 <= y /\ (x * y = 1)
   -> x * y * (x + y) <= x ^ 2 + y ^ 2.
Proof.
  wtransfer'.
  intros ; psatz Z 3.
Qed.

Lemma hol_light18 : forall x y,
  0 <= x /\ 0 <= y -> x * y * (x + y) ^ 2 <= (x ^ 2 + y ^ 2) ^ 2.
Proof.
  wtransfer'.
  intros ; psatz Z 4.
Qed.

(* ------------------------------------------------------------------------- *)
(* Some examples over integers and natural numbers.                          *)
(* ------------------------------------------------------------------------- *)

Lemma hol_light19 : forall m n, 2 * m + n = (n + m) + m.
Proof.
  wrap; tlia.
Qed.

Lemma hol_light22 : forall n, n >= 0 -> n <= n * n.
Proof.
  transfer.
  intros; psatz Z 2.
Qed.


Lemma hol_light24 : forall x1 y1 x2 y2, x1 >= 0 -> x2 >= 0 -> y1 >= 0 -> y2 >= 0 ->
  ((x1 + y1) ^2 + x1 + 1 = (x2 + y2) ^ 2 + x2 + 1)
                -> (x1 + y1 = x2 + y2).
Proof.
  wtransfer'.
  intros; psatz Z 2.
Qed.

Lemma motzkin' : forall x y:int, (x^2+y^2+1)*(x^2*y^4 + x^4*y^2 + 1 - 3*x^2*y^2) >= 0.
Proof.
  wtransfer'.
  intros; psatz Z 1.
Qed.

Lemma motzkin : forall x y:int, (x^2*y^4 + x^4*y^2 + 1 - 3*x^2*y^2)  >= 0.
Proof.
  intros x y; generalize (motzkin' x y); revert x y.
  wtransfer'.
  intros; psatz Z 8.
Qed.
