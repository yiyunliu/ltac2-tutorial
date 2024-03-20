From Ltac2 Require Import Ltac2.
(* Let's write an Ltac2 wrapper for the pick fresh tactic from the metalib *)
Require Import Metalib.Metatheory.

Ltac2 pick_fresh_for (x : ident) (l : constr) :=
  ltac1:( x l |- pick fresh x for l) (Ltac1.of_ident x) (Ltac1.of_constr l).
(* ltac1:(a b |- ...) has the signature Ltac1.t -> Ltac1.t -> unit *)
(* Ltac1.t is an opaque type that represents an untyped Ltac1 argument *)
Ltac2 Eval Ltac1.of_ident.

(* Since pick_fresh_for takes two arguments, we want to use a fancier
   notation *)
Ltac2 Notation "pick" "fresh" x(ident) "for" l(constr) :=
  pick_fresh_for x l.

(* Note that if we declare an notation argument as a constr, then
   whatever we pass in to the notation at that position is implicitly
   quoted. *)
(* TODO: example *)
