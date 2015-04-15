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

To do so use ``Declare Surjection f by (g, proof).`` where ``f : A → B``,
``g : B → A`` and ``proof : ∀ x : B, f (g x) = x`` and specify which
relations are transfered by ``f`` with
``Declare Transfer r to r' by (f, proof).`` where ``r`` has n arguments of
type ``A`` and ``r'`` has n arguments of type ``B``, ``f : A → B``
and ``proof : ∀ x1 ... xn : A, r x1 ... xn → r' (f x1) ... (f xn)``.

Then, in any proof development write ``exact modulo thm.`` to apply the
tactic.

##Internals

##TODO

- Handle backtracking by declaring the appropriate summary and objects.
- Handle transfer in hypotheses
