#Plugin *transfer* for Coq (v8.5)

Introduces a way to declare surjective morphisms between datatypes and
a related tactic called *exact modulo*.
Given a theorem, exact modulo will try to automatically build a proof
that it implies the current goal.

##How to use

````
$ coq_makefile transfer.ml4 -o Makefile
$ make
$ coqide -I .
````

Start your Coq file with the following:

````
Declare ML Module "transfer".
````

In principle, exact modulo is at least as powerful as the *exact* tactic.
To make it more powerful, you first need to declare surjective morphisms.

To do so use ``Declare Surjection f by (g, proof).`` where ``f``, ``g``
and ``proof`` are previously declared identifiers such that ``f : A → B``,
``g : B → A`` and ``proof : ∀ x : B, f (g x) = x`` and specify which
relations are transfered by ``f`` with
``Declare Transfer r to r' by (f, proof).`` where ``r``, ``r'``, ``f``
and ``proof`` are previously declared identifiers such that
``r`` has n arguments of
type ``A`` and ``r'`` has n arguments of type ``B``, ``f : A → B``
and ``proof : ∀ x1 ... xn : A, r x1 ... xn → r' (f x1) ... (f xn)``.

Then, in any proof development write ``exact modulo thm.`` to apply the
tactic.

##Internals

Surjections and transfer lemmas are stored in two tables: one
is a mapping from pairs of types to a surjection, its right-inverse
and a proof of the surjection lemma; the other is a mapping from pairs of
relations to a transfer function and a proof of the transfer lemma.

Example: ``Declare Surjection N.of_nat by (N.to_nat, N2Nat.id).``
adds the following row to the surjection table.

````
+----------+--------------------------------+
| (nat, N) | (N.of_nat, N.to_nat, N2Nat.id) |
+----------+--------------------------------+
````

Types of identifiers in a declaration are checked at the declaration time.

The main algorithm constructs a proof of ``goal`` in a given context,
given a proof ``proofthm`` of a theorem ``thm``. It is described in the
following paper:

* Zimmermann T. and Herbelin H.
*Automatic and Transparent Transfer of Theorems along Isomorphisms in the Coq Proof Assistant.*
Accepted for presentation at CICM 2015 (work-in-progress track).
Read it on [SJS](http://www.sjscience.org/article?id=254),
on [HAL](https://hal.archives-ouvertes.fr/hal-01152588)
or on the [arXiv](http://arxiv.org/abs/1505.05028).

##Example

A simple example is included in the "transfer_Z.v" file.
It highlights that this plugin is able to transfer theorems even between non-isomorphic types,
given that the required declarations are made.

