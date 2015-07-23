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
