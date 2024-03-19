# ltac2-tutorial
A simple `Ltac2` tutorial that is intended to supplement the official documentation with an extensive set of examples.

The code is known to compiles under Coq 8.16.0 and 8.18.0. If you are using an older version of Coq, certain standard library functions or language constructs might be missing (e.g. `Int.le` and `if`).

- [tutorial](tutorial.v) contains the basics of Ltac2. The metalib example requires the package [metalib](https://github.com/plclub/metalib), though feel free to comment it out if you don't have it installed. I plan to replace the example with something else that is dependency free.
- [tutorial2](tutorial2.v) showcases the proof by reflection technique described in [Cpdt.Reflection](http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html).
