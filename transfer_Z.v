(* To load with:
   $ coqide -I . transfer_Z.v
 *)

(* Preliminary declarations *)

Declare ML Module "transfer".

Require Import ZArith.

Declare Surjection Z.to_nat by (Z.of_nat, Nat2Z.id).

Declare Transfer le to Z.le by (Z.of_nat, inj_le).

Theorem le_transf_back :
  forall x y, (x <= y)%Z -> Z.to_nat x <= Z.to_nat y.
Proof.
  intros.
  destruct x; auto with arith.
  apply Z2Nat.inj_le; auto with zarith.
  transitivity (Z.pos p); auto with zarith.
Qed.

Declare Transfer Z.le to le by (Z.to_nat, le_transf_back).

(* Two examples of theorems transfered *)

Theorem le_refl_transf : forall n : nat, n <= n.
Proof.
  exact modulo Z.le_refl.
Qed.

Theorem le_trans_transf :
  forall n m p : nat, n <= m -> m <= p -> n <= p.
Proof.
  exact modulo Z.le_trans.
Qed.

(* Mixing several relations *)

Declare Transfer lt to Z.lt by (Z.of_nat, inj_lt).

Theorem lt_le_incl_transf :
  forall n m : nat, n < m -> n <= m.
Proof.
  exact modulo Z.lt_le_incl.
Qed.
