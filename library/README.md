#Transfer library for Coq

This library helps you working seamlessly with several representations
for the same objects, switching from one to another when doing proofs
and easily transferring theorems across representations.

A typical workflow would be the following:
- You define two new types and a few functions on them.
- You relate the two types and their functions by adequate transfer
declarations.
- You prove your theorems only once (on the most suited representation)
and if you need to use them on the other representation, instead of
doing ``exact my_thm``, you do ``exact (modulo my_thm)`` and the library
takes care of the transfer.
- Finally, if you have defined your transfer rules properly, you may
also be able to change your current proof goal from one representation
to the other by doing ``apply modulo`` (this may not work well if you
have more than two related representations). This way of using the
transfer library was inspired by Isabelle ``transfer'`` tactic.

##Transfer declarations

First, you need to define a relation between the two types you consider:
``R : A -> B -> Prop``.
If you are given a function from one type to the other, say ``f : A -> B``,
you may define ``R x y := f x = y``.

Then you need to declare properties of this relation, such as injectivity
(right-uniqueness), functionality (left-uniqueness), surjectivity
(right-totality) and (left-)totality.

The corresponding declarations should look like this:

````
Instance injectivity_of_R : Related (R ##> R ##> flip impl) (@eq A) (@eq B).

Instance functionality_of_R : Related (R ##> R ##> impl) (@eq A) (@eq B).

Instance surjectivity_of_R : Related ((R ##> impl) ##> impl) (@all A) (@all B).

Instance totality_of_R : Related ((R ##> flip impl) ##> flip impl) (@all A) (@all B).
````

[Transfer.v](Transfer.v) contains proofs that the last two declarations correspond
indeed to surjectivity and totality theorems.

If some of these properties are not true for relation R, it may be possible to
prove variants, for instance replacing equality with another equivalence
or universal quantification with some bounded quantification.

###Compatibility with functions and relations

Here are some examples of such declarations:

````
Instance compat_with_binary_op : Related (R ##> R ##> R) bin_op_A bin_op_B

Instance compat_with_internal_function : Related (R ##> R) fun_A fun_B

Instance compat_with_external_function : Related (R ##> eq) fun_from_A fun_from_B

Instance compat_with_binary_relation_one_way : Related (R ##> R ##> impl) bin_rel_A bin_rel_B

Instance compat_with_binary_relation_other_way : Related (R ##> R ##> flip impl) bin_rel_A bin_rel_B
````

##Use of the library

###Transfer of theorems

You can see examples of transferred theorems in [NArithTests.v](NArithTests.v).
Theorems which have the same form but for related objects (in particular, quantification is
on two different types), you can prove only one of them and use
``exact (modulo my_proved_thm)`` to get a proof of the other.
This will unify the current goal with ``my_proved_thm`` modulo some known relations
(previously declared as instances of ``Related``).

##Change of representation

``modulo`` is a very general theorem:
````
modulo : ?t -> ?u
where
?t : [ |- Prop]
?u : [ |- Prop]
?class : [ |- Related impl ?t ?u]
````

By calling it through ``exact (modulo thm)`` you are providing it with the values
of ``?t`` and ``?u`` and it just has to infer a proof of ``Related impl ?t ?u``
from the known ``Related`` instances.
Another use however is to call ``apply modulo`` inside a proof development, thus
providing ``?u`` but not ``?t``. In some cases, it will be able to also infer
the value of ``?t`` and leave you with a transformed goal, thus effectively
operating a change of representation.
Since it is a more complicated task, it might also fail, or leave you a transformed
goal which does not correspond to what you wanted (in particular when your type
is related to several other types).