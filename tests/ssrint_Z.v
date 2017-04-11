From Transfer Require Import Transfer ssrint_Z.
From mathcomp Require Import ssrint ssrnum ssralg ssrbool.

Lemma s : forall (x y z t : int), (x < y -> z < t -> x + z < y + t)%R.
Proof.
  Timeout 1 (transfer; fail) + idtac.
  Local Notation "x < y" := (BinInt.Z.lt x y).
  Local Notation "x + y" := (BinInt.Z.add x y).
  transfer.
  now_show (forall (x y z t : BinNums.Z), x < y -> z < t -> x + z < y + t).
Abort.
