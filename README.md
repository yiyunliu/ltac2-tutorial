# Ltac2 tutorial
A simple `Ltac2` tutorial that is intended to supplement the official documentation with an extensive set of examples. You can find the rendered html version (still WIP) at <https://blog.electriclam.com/ltac2/toc.html>.

The code is known to compiles under Coq 8.16.0 and 8.18.0. If you are using an older version of Coq, certain standard library functions or language constructs might be missing (e.g. `Int.le` and `if`).

You can contribute by making pull requests or simply asking me to add you as a contributor. I'm still working to turn the comments in the Coq code into coqdoc.

- [tutorial0](theories/tutorial0.v) contains the basics of Ltac2. You'll learn about how to write and evaluate expressions, define algebraic data types, and interface with the API that allows you to manipulate the proof states and define tactics.
- [tutorial1](theories/tutorial1.v) showcases the proof by reflection technique described in [Cpdt.Reflection](http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html).
- [tutorial2](theories/tutorial2.v) is still WIP and is supposed to show how to write wrappers for Ltac1 tactics in Ltac2. The file uses Ltac1 tactics from the package [metalib](https://github.com/plclub/metalib) as an example, though eventually I'll replace the example with something that is self-contained and does not require any external dependencies.
