#Plugin *transfer* for Coq (v8.5)

Introduces a way to declare surjective morphisms betweem datatypes and
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
Declare ML Module "t".
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

Surjections and transfer lemmas are stored in two tables: the former
is a mapping from pairs of types to the surjection, its right-inverse
and the proof of the lemma; the latter is a mapping from pairs of
relations to the transfer function and the proof of the lemma.

Example: ``Declare Surjection N.of_nat by (N.to_nat, N2Nat.id).``
adds the following row to the surjection table.

````
+----------+--------------------------------+
| (nat, N) | (N.of_nat, N.to_nat, N2Nat.id) |
+----------+--------------------------------+
````

Types of identifiers in a declaration are checked at the declaration time.

The main algorithm constructs a proof of ``goal`` in a given context,
given a proof ``proofthm`` of a theorem ``thm``.
To do so, it matches the forms of ``goal`` and ``thm``. So far there are
three main cases:

- ``thm`` has the form ``∀ x : A, B[x]`` and ``goal`` has the form
``∀ x : A, B'[x]``. Then we recurse to find a proof ``p_rec[P_b]``
of ``B'[x]``
and we return the proofterm ``λ x : A, p_rec[proofthm x]``.
- ``thm`` has the form ``∀ x : A', B[x]`` and ``goal`` has the form
``∀ x' : A', B'[x]``. Then we find the surjection ``(f, g, proofsurj)``
associated to ``(A, A')``. If it does not exist, we fail.
If it exists, we recurse to find a proof ``p_rec[P_b]``
of ``B'[f (g x)]``
and we return the proofterm
``λ x : A, eq_rect (f (g x)) B' p_rec[proofthm (g x)] x proofsurj``.
- ``thm`` has the form ``R x1 ... xn`` and ``goal`` has the form
``R' x1 ... xn``. Then we find the transfer ``(f, prooftransf)``
associated to ``(R, R')``. If it does not exist, we fail.
If it exists, we return the proofterm ``prooftransf x1 ... xn proofthm``.

In all the other cases, the algorithm tries to unify ``goal`` and ``thm``
and returns ``proofthm`` in case of success and an error otherwise.

##TODO

- Handle transfer in hypotheses
