# Transfer library for Coq

⚠️ **This library is not maintained.** ⚠️
The most similar tool available for Coq is probably the [CoqEAL library](https://github.com/CoqEAL/CoqEAL) refinements module.

The most up-to-date documentation for this library is [the presentation
I made at the Deducteam seminar
(April, 2017)](http://www.theozimmermann.net/transfer/deducteam-seminar/)
(whose sources you can find in the *slides-deducteam* branch of this
repository). The README below hasn't been updated for a longer period.

This library helps you working seamlessly with several representations
for the same objects, switching from one to another when doing proofs
and easily transferring theorems across representations.

A typical workflow would be the following:
- You define two new types and a few functions on them.
- You relate the two types and their functions by adequate transfer
declarations.
- You prove your theorems only once (on the most suited representation)
and if you need to use them on the other representation, instead of
doing ``exact my_thm``, you do ``exactm my_thm`` and the library
takes care of the transfer.
- Similarly, you can use ``applym my_thm`` instead of ``apply my_thm``
but it is not guaranteed to work with any type of theorem.
- Finally, if you have defined your transfer rules properly, you may
also be able to change your current proof goal from one representation
to the other by doing ``transfer`` (this may not work well if you
have more than two related representations). This way of using the
transfer library was inspired by Isabelle's ``transfer'`` tactic.

## Transfer declarations

First, you need to define a relation between the two types you
are considering:
``R : A -> B -> Prop``.
If you are given a function from one type to the other, say ``f : A -> B``,
you may define ``R x y := f x = y``.

Then you need to declare properties of this relation, such as injectivity
(right-uniqueness), functionality (left-uniqueness), surjectivity
(right-totality) and (left-)totality.

The corresponding declarations should look like this:

```coq
Instance injectivity_of_R : Related (R ##> R ##> flip impl) (@eq A) (@eq B).

Instance functionality_of_R : Related (R ##> R ##> impl) (@eq A) (@eq B).

Instance surjectivity_of_R : Related ((R ##> impl) ##> impl) (@all A) (@all B).

Instance totality_of_R : Related ((R ##> flip impl) ##> flip impl) (@all A) (@all B).
```

[Respectful.v](Respectful.v) contains theorems relating these kinds of declarations
to more familiar statements.

If some of these properties are not true for relation ``R``, it may be possible to
prove variants, for instance replacing equality with another equivalence
or universal quantification with some bounded quantification.

If all these properties are true, then they can be expressed in a simpler way in only
two properties:

```coq
Instance bitotal_R : Related ((R ##> iff) ##> iff) (@all A) (@all B).

Instance biunique_R : Related (R ##> R ##> iff) (@eq A) (@eq B).
```

### Compatibility with functions and relations

Here are some examples of such declarations:

```coq
Instance compat_with_binary_op : Related (R ##> R ##> R) bin_op_A bin_op_B.

Instance compat_with_internal_function : Related (R ##> R) fun_A fun_B.

Instance compat_with_external_function : Related (R ##> eq) fun_from_A fun_from_B.

Instance compat_with_binary_relation_one_way : Related (R ##> R ##> impl) bin_rel_A bin_rel_B.

Instance compat_with_binary_relation_other_way : Related (R ##> R ##> flip impl) bin_rel_A bin_rel_B.
```

NB: for now, all these declarations will be good only for transferring
theorems from ``A`` to ``B``. If you need to go both ways, you should
add the corresponding reversed declarations, even when they are equivalent.
For instance:

```coq
Instance compat_with_binary_op' : Related (flip R ##> flip R ##> flip R) bin_op_B bin_op_A.
```

## Usage of the library

### Transfer of theorems

You can see examples of transferred theorems in [NArithTests.v](NArithTests.v).
When two theorems have the same form but for related objects (in particular, quantification is
on two different types), you can prove only one of them and use
``exactm my_proved_thm`` to get a proof of the other.
This will unify the current goal with ``my_proved_thm`` modulo some known relations
(previously declared as instances of ``Related``).

## Change of representation

``modulo`` is a very general theorem:

```coq
modulo : ?t -> ?u
where
?t : [ |- Prop]
?u : [ |- Prop]
?class : [ |- Related impl ?t ?u]
```

By calling it through `exactm thm` which is just sugar for `exact (modulo thm)`
you are providing it with the values
of ``?t`` and ``?u`` and it just has to infer a proof of ``Related impl ?t ?u``
from the known ``Related`` instances.
Another use however is to call `transfer` (just sugar for `apply modulo`)
inside a proof development, thus
providing ``?u`` but not ``?t``. In some cases, it will be able to also infer
the value of ``?t`` and leave you with a transformed goal, thus effectively
operating a change of representation.
Since it is a more complicated task, it might also fail, or leave you a transformed
goal which does not correspond to what you wanted (in particular when your type
is related to several other types).

Here is an example of how it can be used to go beyond `exactm thm)`:

```coq
Require Import NArithTransfer.

Goal forall x1 y1 z1 : N, x1 = y1 -> N.add x1 z1 = N.add y1 z1.
Proof.
  transfer. (* Now the goal is: forall x x0 x1 : nat, x = x0 -> x + x1 = x0 + x1 *)
  intros.
  Check f_equal2_plus. (* f_equal2_plus : forall x1 y1 x2 y2 : nat, x1 = y1 -> x2 = y2 -> x1 + x2 = y1 + y2 *)
  apply f_equal2_plus; trivial.
Qed.
```

There is an implementation problem which makes it difficult handling theorems
where there is no implication under the quantifiers. To work around this
limitation, it may be useful to insert dummy hypotheses as in the following example:
```coq
Require Import NArithTransfer.

(** ** Basic specifications : pred add sub mul *)

Goal forall n, N.pred (N.succ n) = n.
Proof.
  enough (forall n, True -> N.pred (N.succ n) = n) by firstorder. (* Adding dummy hypothesis *)
  trasnfer. (* Now the goal is: forall n : nat, True -> Nat.pred (S n) = n *)
  intros n _.
  apply PeanoNat.Nat.pred_succ.
Qed.
```

# Bibliography

* Zimmermann T. and Herbelin H.
*Automatic and Transparent Transfer of Theorems along Isomorphisms in the Coq Proof Assistant.*
Presented at CICM 2015 (work-in-progress track).
Read it
on [HAL](https://hal.archives-ouvertes.fr/hal-01152588)
or on [arXiv](http://arxiv.org/abs/1505.05028).

NB: you can find the *plugin* described in this paper in the *plugin* branch of this repository.
