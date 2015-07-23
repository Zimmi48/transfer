#Automatic transfer of theorems in Coq

This repository contains two directories, [*plugin*](plugin) and [*library*](library).

The two contain independent implementations of ways of transferring theorems but
[*library*](library) is more recent, much more powerful
(it can transfer all kinds of theorems
whereas the first one was limited to theorems containing only foralls, implications
and relations) and easier to load (since it is just a library). Thus, unless you
have a good reason not to, you should use [*library*](library).

Each directory contains instructions on how to use.

The ideas behind the two are described in the following paper:

* Zimmermann T. and Herbelin H.
*Automatic and Transparent Transfer of Theorems along Isomorphisms in the Coq Proof Assistant.*
Presented at CICM 2015 (work-in-progress track).
Read it on [SJS](http://www.sjscience.org/article?id=254),
on [HAL](https://hal.archives-ouvertes.fr/hal-01152588)
or on the [arXiv](http://arxiv.org/abs/1505.05028).

