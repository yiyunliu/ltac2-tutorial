(** * Ltac2 Quickstart *)

(** Ltac2 is a new language for writing tactics in Coq. Unlike its
 predecessor Ltac, Ltac2 supports features such as data types, static typing, and
a more readable syntax for metaprogramming. The goal of this document is to introduce
the basic features of Ltac2 as an ML-family functional programminig language,
and the APIs that would allow you to write tactics by modifying the proof state.  *)

(** Before we start the tutorial, we first require and import the Ltac2 library.  *)
From Ltac2 Require Import Ltac2.

(** For reasons we will discuss later, if you are eager to try out Ltac2 on an existing Rocq project,
 you should run the following command right after the Ltac2 import so your existing scripts don't break  *)
Set Default Proof Mode "Classic".

(** ** Functional Programming with Ltac2 *)

(** *** Basics *)

(** The main purpose of Ltac2 is a metaprogramming language for constructing Gallina terms, which are terms
 that we use in our Rocq definitions and proof objects. The definitions of Ltac2 and Gallina live in
 different namespaces. To write Ltac2 definitions, we use commands that are prefixed [Ltac2] *)

Ltac2 two : int := 2.

(** The command above binds the Ltac2 variable [two] to the number [2] of type [int]. Unlike Ltac,
Ltac2 is statically typed. When the type annotation is omitted, the type is inferred. *)

Ltac2 three := 3.

(** We can query the type of an Ltac2 term using the command [Ltac2 Check], analogous to how we use
 the [Check] command to query the type of Gallina terms. *)

Ltac2 Check two.
Ltac2 Check three.
(** Unsurprisingly, both [two] and [three] share the type [int]. *)

(** The [Ltac2 Eval] command allows us to evaluate an Ltac2 expression.  *)
Ltac2 Eval Int.add (Int.add two three) two.
(** We get the integer [7] from adding up [2], [3], and [2]  *)

(** Note that the [+] symbol is not part of the syntax of Ltac2 for integer addition.
 We need to use the [Int.add] function from the Ltac2 standard library to add up Ltac2 integers. *)

(** The [Int] module was made available from the earlier [Requrie Import] command. We can also import the
 [Int] module itself so we don't have to write the [Int] qualifier for add. *)
Import Int.
Ltac2 Eval add two two.

(** The syntax for defining Ltac2 functions is almost the same as the syntax for Gallina functions.
 Here are some different ways of defining a function that doubles its input. *)

Ltac2 double := fun x => add x x.

Ltac2 double' x := add x x.

Ltac2 double'' (x : int) : int := add x x.

Ltac2 double''' := fun (x : int) => add x x.

(** We can also use let bindings in our definition. *)

Ltac2 quadruple x :=
  let twice f x := f (f x) in
  twice double x.

Ltac2 Eval quadruple 4.

(** The Hindley-Milner inference algorithm allows us to write
 polymorphic functions with few annotations. *)

Ltac2 identity x := x.

Ltac2 Check identity.
(** Here, the ['a] stands for a type parameter, which can be
 instantiated to the type of the argument of the [identity] function. *)
Ltac2 Eval identity 10.
Ltac2 Eval identity double.

(** The [rec] keyword allows us to define recursive functions. Here,
 we define the factorial function [fact] over integers, making use of
 the library functions [le], [mul], and [sub] from the [Int] module
 of the [Ltac2] library, which you can find #<a href="https://rocq-prover.org/doc/V9.0.0/corelib/Ltac2.Int.html">here</a>. *)

Ltac2 rec fact x :=
  if le x 0 then 1 else mul x (fact (sub x 1)).

Ltac2 Eval fact 10.

(** The [rec] keyword can also be used in conjunction with the [let]
keyword to define local recursive functions. Let's use [let rec] to
 define a more efficient tail-recursive version of [fact]. *)

Ltac2 fast_fact x :=
  let rec go x acc :=
    if le x 0 then acc else
      go (sub x 1) (mul x acc) in
  go x 1.


(** Ltac2, like its predecessor Ltac, does not enforce termination checking. *)
Ltac2 rec loop x := loop x.
Ltac2 Check loop.
(** Evaluate [loop 0] (or [loop] with any argument) at your own risk,
 as Rocq would get stuck in an infinite loop! *)


(** In addition to functions and integers, Ltac2 supports
 built-in product types. The constructor takes the form [(a,b)].
 The eliminators [fst] and [snd] allows us to extract out the
 first component [a] and the second component [b] respectively. *)
Ltac2 Eval (1 , 2).
Ltac2 Eval fst (1 , 2).
Ltac2 Eval snd (1 , 2).

(** *** Recursive data types and records *)

(** Like Haskell and OCaml, Ltac2 supports algebraic data types. *)
(** Let's start by defining a simple type [coin], which has
two constructors [Head] and [Tail]. Note that the constructors must
 be capitalized. *)
Ltac2 Type coin := [Head | Tail].
Ltac2 Check Head.
Ltac2 Check Tail.

(** We can eliminate values of an algebraic data type through
pattern matching,  which has a syntax that is very similar to [match]
 for Gallina terms. *)

Ltac2 flip x :=
  match x with
  | Head => Tail
  | Tail => Head
  end.

(** In case you haven't noticed, if you forgot a specific piece
 of Ltac2 syntax, you can always make an educated guess if you are
 already familiar with OCaml or Gallina. *)

(** We can also define recursive data types by including the [rec]
keyword. Here's how we define the nat type for [Ltac2]. Note that the
parentheses around [pnat] in [S (pnat)] is not optional.  *)

Ltac2 Type rec pnat := [Z | S (pnat)].

Ltac2 Eval Z.
Ltac2 Eval (S (S Z)).

(** We can write a recursive function that adds two peano numbers.
 We name our function [padd] to disambiguate it from the [add] we
 imported from the [Int] module. *)
Ltac2 rec padd x y :=
  match x with
  | Z => y
  | S x => S (padd x y)
  end.

Ltac2 Eval padd (S (S Z)) (S Z).


(** As an exercise, rewrite the definitions of [to_int] so
 it converts from a peano number to its integer representation *)
Ltac2 rec to_int (x : pnat) := 0.

(* Should return 2 *)
Ltac2 Eval to_int (S (S Z)).

(** For the next example, let us consider a
 binary tree which stores integers. *)

Ltac2 Type rec int_tree :=
  [ IEmpty | INode (int, int_tree, int_tree) ].

(** The leaf constructor [Empty] takes no argument.
The [Node] constructor takes three arguments, including an
 [int], and its two child nodes. These arguments are separated
 by comma, which is quite different from Gallina's syntax, but the
pattern matching form works the same way regardless. *)

Ltac2 rec mirror (t : int_tree) : int_tree  :=
  match t with
  | IEmpty => IEmpty
  | INode x l r => INode x (mirror r) (mirror l)
  end.

Ltac2 singleton x := INode x IEmpty IEmpty.

Ltac2 Eval mirror (INode 1 (INode 2 (singleton 3) (singleton 4))
                     (singleton 5)).


(** We can generalize the [int_tree] definition to the following [tree] data type,
 which abstracts the [int] type with a type parameter ['a] *)

Ltac2 Type rec 'a tree :=
  [Empty | Node ('a, 'a tree, 'a tree)].

(** Note that the type arguments to the type constructor [tree] preceeds the type constructor itself.
A tree of booleans, for example, is written as [bool tree] instead of [tree bool]. *)
Ltac2 Check (Empty : bool tree).

(** If your data type is parameterized by multiple type parameters, you need to put them together
 with parentheses. For example, here's how we define our own pair type *)
Ltac2 Type ('a, 'b) mypair := [Pair ('a , 'b)].

Ltac2 Check Pair 1 true.

(** We can recover the projection operators through pattern matching.  *)
Ltac2 myfst a :=
  match a with
  | Pair x y => x
  end.

Ltac2 mysnd a :=
  match a with
  | Pair x y => y
  end.

(** Again, thanks to the Hindley-Milner style inference, our functions are automatically polymorphic
 without any explicit annotations. *)
Ltac2 Check myfst.
Ltac2 Check mysnd.
Ltac2 Eval myfst (Pair 1 true).
Ltac2 Eval mysnd (Pair 1 true).

(** A side note: since [Pair] has only one constructor, we can directly pattern match
 in function arguments. *)
Ltac2 myfst' (Pair a _) := a.
Ltac2 myfst'' := fun (Pair a _) => a.


(** A different (and perhaps better) way of defining pairs is to use a record type definition,
 where we specify the data type by specifying the fields the type contains.  *)
Ltac2 Type ('a, 'b) RPair := {rfst : 'a; rsnd : 'b}.

(** To construct a value of a record type, we specify what the individual fields should be. *)
Ltac2 Eval {rfst := 4; rsnd := 9}.

(** Of course, we can always define a constructor to save some typing.  *)
Ltac2 rpair a b := {rfst := a; rsnd := b}.
(** The following ltac2 expression evaluates to the same pair containing 4 and 9 *)
Ltac2 Eval rpair 4 9.

(** We can project out individual component by appending a record value with .(fieldname)  *)
Ltac2 Eval {rfst := 4; rsnd := 9}.(rfst).
Ltac2 Eval {rfst := 4; rsnd := 9}.(rsnd).

(** We can define the following [swap] function that swaps the first and second components of a pair *)
Ltac2 swap a := rpair (a.(rsnd)) (a.(rfst)).

Ltac2 Eval swap (rpair true 1).

(** The [rec] keyword also works for record types. Here's how we can define an infinite stream type.
 Note that the tail is defined as a function that maps a trivial unit input to another stream.
 We need to use the trivial function arrow to "thunk" the tail since Ltac2 is strict  *)
Ltac2 Type rec 'a stream :={shead : 'a ; stail : unit -> 'a stream }.

(** We can access the actual tail of the list by passing it the unit value [()].  *)
Ltac2 snext a := a.(stail) ().

(** We define the sequence of numbers n, n + 1, n + 2, ... as follows *)
Ltac2 rec incr_seq n :=
  {shead := n ; stail := fun _ => incr_seq (add 1 n)}.

Ltac2 Eval snext (incr_seq 4).
Ltac2 Eval snext (snext (snext (snext (incr_seq 4)))).

(** *** Data types from the standard library  *)
(** The standard library of Ltac2 already includes some useful
data types, including [bool] and [list]. We can print out
 their definitions using the [Print Ltac2 Type] command. *)
Print Ltac2 Type bool.
Print Ltac2 Type list.

(** Both data types come with special syntactic forms,*)
Ltac2 Eval if true then 1 else 2.
Ltac2 Eval [1;2;3].

(** and library functions.  *)
Ltac2 Eval List.length [1;2;3].
Ltac2 Eval Bool.or true false.
Ltac2 Eval List.fold_right add [1;2;3;4;5] 0.
Ltac2 Eval List.fold_right mul [1;2;3;4;5] 1.

(** You can check the definitions of those library functions with
 the command [Print Ltac2] *)

Print Ltac2 List.length.
Print Ltac2 Bool.or.

(** In general, you can find the documentations of the library
functions from the #<a href="https://rocq-prover.org/doc/V9.0.0/corelib/index.html">reference manual for the standard library</a> by
 searching the keyword "Ltac2". *)

(** ** Interacting with proof states   *)

(** *** Constructing and Matching Gallina Terms *)

(** The standard library of Ltac2 exposes APIs that allow the programmer to use Ltac2 to construct
Gallina/Rocq terms and manipulate proof states. *)

(** Let us start by constructing the Gallina term 1 + 2. *)
Ltac2 two_plus_one () := '(1 + 2).
Ltac2 Check two_plus_one.

(** In the definition  of [two_plus_one], we use a special syntax where we write [()] when a
 function parameter is expected. This syntax tells Ltac2 that our function takes the unit value [()] as
 its input. *)

(** The [constr] data type is an opaque ltac2 data type used to represent Gallina terms.
To tell Ltac2 that we are defining a Gallina term, we wrap the expression with '(...). *)

(** To be able to retrieve the term, we need to pass the unit value [()] to [two_plus_one]  *)
Ltac2 Eval two_plus_one ().


(** Why must we define [two_plus_one] as a function instead of a constant of type [constr]?
 In Ltac2, top-level definitions must be a value. Instead of knowing precisely what values are,
it is helpful to think of the values as Ltac2 expressions that do not evaluate on their own.
For example, the following definitions are valid. *)
Ltac2 int_val := 1.
Ltac2 func_val := fun x y => add x (add y y).
(** In [int_val], the integer value doesn't really compute on its own. In [func_val], the function
 doesn't evaluate/reduce unless we pass it two integer arguments. *)

(** The following definition is an invalid top-level definition, because its body involves the
call to the [add] function.  *)
Fail Ltac2 bad_val := add 1 3.

(** The following function definition is invalid, because the lambda is nested in a computation  *)
Fail Ltac2 bad_func' := let x := add 1 3 in fun y => add x y.

(** What about [constr]? Why is ['(1 + 2)] not count as a value? It turns out that when we construct
 Gallina terms, Ltac2 always type checks the term, which may fail. *)
Ltac2 bad_term () := '(1 + true).
Fail Ltac2 Eval bad_term ().

(** Therefore, for top-level Ltac2 definitions of Gallina terms,
    we can only write functions that, if successfully returns, give us back a well-typed Gallina term. *)

(** However, local definitions or expressions we send to [Ltac2 Eval] don't subject to the same restriction.  *)
Ltac2 Eval let x := '(1 + 1) in x.
Ltac2 Eval '(1 + 1).

(** If you don't understand why just yet, you can simply write definitions without thinking about
 the unit parameter, and if your definition is invalid, Ltac2 will give you an error message to remind you to
 add a [()]. *)

(** Given an Ltac2 variable of type [constr], we can use the [$var] syntax to interpolate the
 variable inside a Gallina expression we are constructing. *)
Ltac2 Eval let x := '(1 + 1) in '($x * 2).

(** The $ symbol tells Ltac2 that the variable [x] is an Ltac2 variable. Omitting the $ results in
 an error as there's no top-level Gallina definition named [x]. *)
Fail Ltac2 Eval let x := '(1 + 1) in '(x * 2).
(** In fact, Rocq will give a warning that the variable [x] is unused, as the [x] in [(x * 2)] refers to
 a Gallina variable [x], which is not in the same namespace as Ltac2 variables. *)

(** As an exercise, given the following Gallina definition of [x], check the result of
 the following [Ltac2 Eval] command and see if the return value is as expected. *)
Notation x := (4).

Ltac2 Eval let x := '(1 + 1) in '(x * $x).

(** The [constr] type is opaque and therefore we cannot directly examine the ast of a Gallina term
 by pattern matching a value of type [constr]. *)

(** Instead, we use the [lazy_match!] construct to match [constr] terms.  *)

Ltac2 lhs_of (x : constr) :=
  lazy_match! x with
  | ?a + ?b => a
  | ?a * _ => a
  end.

Ltac2 Eval lhs_of '(100 + 2).
Ltac2 Eval lhs_of '(44 * 7).

(** The [lazy_match!] syntactic form takes a Gallina term of type [constr]. For each branch, we
 write patterns that involve Gallina terms with the binders prefixed with a question mark.
 When we don't care what a term is, we can use the wildcard pattern [_], as we did in the multiplcation
 case. *)

(** The pattern matching does not have to be exhaustive. If we invoke [lhs_of] on a term that doesn't
 match any of the patterns, we end up with a [Match_failure] exception. *)
Fail Ltac2 Eval lhs_of '(4 - 3).

(** We can write more sophisticated functions such as the following, which mirrors the operands of the [+]
 operator. *)
Ltac2 rec mirror_plus (tm : constr) :=
  lazy_match! tm with
  | ?a + ?b =>
      let rev_b := mirror_plus b in
      let rev_a := mirror_plus a in
      '($rev_b + $rev_a)
  | _ => tm
  end.

Ltac2 Eval mirror_plus '(1 + 8 + 4 + 5).

(** Instead of directly manipulating [constr], we can leverage Ltac2 data types for domain-specific
problems. We use the [Arith] data type to represent the arithmetic expressions we wish to manipulate. *)
Ltac2 Type rec Arith := [Num (constr) | Add (Arith, Arith) ].

(** We write the following function that converts from [constr] to [Arith].  *)
Ltac2 rec to_arith (a : constr) : Arith :=
  lazy_match! a with
  | ?l + ?r =>
      let l' := to_arith l in
      let r' := to_arith r in
      Add l' r'
  | _ => Num a
  end.

Ltac2 Eval to_arith '(1 + 8 + 4 + 5).

(** The mirroring operation can then be carried out on [Arith] through the [match] form. *)
Ltac2 rec mirror_arith (a : Arith) :=
  match a with
  | Num _ => a
  | Add a b => Add (mirror_arith b) (mirror_arith a)
  end.

Ltac2 Eval mirror_arith (to_arith '(1 + 8 + 4 + 5)).

(** The following function converts the [Arith] expressions back to Gallina terms  *)
Ltac2 rec from_arith (a : Arith) :=
  match a with
  | Num n => n
  | Add l r =>
      let l' := from_arith l in
      let r' := from_arith r in
      '($l' + $r')
  end.

(** We can then give an alternative definition of [mirror_plus], which composes all the functions
 we have defined so far. *)
Ltac2 mirror_plus' a := from_arith (mirror_arith (to_arith a)).
Ltac2 Eval mirror_plus' '(1 + 8 + 4 + 5).

(** For a function as simple as [mirror_plus], our setup for [mirror_plus'] is an overkill.
For bigger projects, leveraging the Ltac2 data type makes it more convenient to analyze
 and transform Gallina terms. *)

(** *** Writing Tactics  *)
(** In the previous section, we learned how to construct and match Gallina terms. In this section,
 we learn how to use Ltac2 to help us write Rocq definitions or proofs.  *)

(** Let's start with the following simple statement.  *)

Lemma simple : forall (A B : Prop), A -> B -> A.

  (** Using the intros tactic, we can add the hypotheses to our proof context. *)
  intros A B h0 h1.
  (** The #<a href="https://rocq-prover.org/doc/V9.0.0/corelib/Ltac2.Control.html">Control</a>
      module from Ltac2 contains functions that can query and manipulate the proof state.  *)
  (** For example, the [Control.hyps] function allows us to see the list of hypotheses in the context. *)
  Ltac2 Eval Control.hyps ().
  (** The [Control.hyps] functions returns a list of tuples, containing the name of the hypotheses,
   its body if it has one, and its type. *)

  (** The [Control.refine] function takes a computation/thunk that returns a Gallina term, and tries to
   use that term to complete the goal. Instead of using Ltac2 Eval,
   we use the [ltac2:(...)] form, which takes an Ltac2 expression of type [unit], which, when executed,
   can modify the proof state. *)
  ltac2:(Control.refine (fun _ => 'h0)).
Qed.

(** Recall the flag we set near the beginning of the tutorial.  *)
Set Default Proof Mode "Classic".
(** By setting the default proof mode to "Classic", Rocq expects the proof script to be written in
 Ltac. As a consequence, the expression [Control.refine (fun _ => 'h0)] must be wrapped in [ltac2:(...)]
to remind Rocq that we are writing Ltac2, not Ltac.
Without the [Set Default ...] command, importing Ltac2 will set the proof mode to "Ltac2". As of today,
having Ltac2 as the default proof mode is not very desirable, since many tactic libraries (e.g. CoqHammer,
mathcomp) are only available in Ltac. More likely, your proof script will break with "Ltac2" being the
default proof mode. *)

Set Default Proof Mode "Ltac2".
Goal forall (A B : Prop), A -> B -> A.
  Fail tauto.
  (* Fails with an error: Unbound value tauto *)
  (* the tauto tactic is not yet available in Ltac2 *)
Abort.

Set Default Proof Mode "Classic".
Goal forall (A B : Prop), A -> B -> A.
  tauto.
Qed.

(** A more realistic workflow would involve defining complex tactics in Ltac2, and export the
Ltac2 tactic to Ltac1 through FFI. We demonstrate this workflow by defining a naive implementation
of the [assumption] tactic, which completes the goal by searching for a hypothesis that has
a matching type. *)


(** The [find_assumption] function returns the identifier of the hypothesis whose type matches the
 goal by composing several library functions. [Control.goal] gives the type of the goal.
 [List.find] takes a boolean predicate and returns the first element of the input list where the
 predicate holds. [Constr.equal] checks the alpha-equivalence of two Gallina terms. *)

Ltac2 find_assumption () : ident :=
  let g := Control.goal () in
  let h := List.find (fun (_,_,ty) => Constr.equal g ty) (Control.hyps ()) in
  match h with
  | (h_ident, _, _) => h_ident
  end.

(** Our full tactic is defined as follows, where [Control.hyp] converts an identifier to a Gallina term,
 which Control.refine expects as the return value of its input thunk *)
Ltac2 myassumption' () :=
  Control.refine (fun _ => Control.hyp (find_assumption ())).

(** We can already use [myassumption] in our proof script, though it is quite verbose to write the ltac2
 boilerplate. *)
Goal forall (A B : Prop), A -> B -> A.
Proof.
  intros.
  ltac2:(myassumption' ()).
Qed.

(** The first thing we can do is to wrap [myassumption] inside an Ltac2 Notation so we don't have to
 write the trailing parentheses. *)
Ltac2 Notation "myassumption" := myassumption' ().

Goal forall (A B : Prop), A -> B -> A.
Proof.
  intros.
  ltac2:(myassumption).
Qed.

(** In the example, I named the function [myassumption']  differently from the notation [myassumption]. *)
(** It is perfectly fine to shadow the original function name with a notation of the same name.  *)
Ltac2 Notation "myassumption'" := myassumption' ().
Goal forall (A B : Prop), A -> B -> A.
  intros.
  Fail ltac2:(myassumption' ()).
  ltac2:(myassumption').
Qed.
(** However, what if we need to refer to the old function, which hasn't been applied to unit?
 We can always rethunk it as follows. *)
Ltac2 Eval (fun () => myassumption').

(** At this point, we still haven't gotten rid of the [ltac2:] from our proof script. Without [ltac2:(...)],
 Rocq will complain as [myassumption] is not an Ltac1 tactic. *)
Goal forall (A B : Prop), A -> B -> A.
  intros.
  Fail myassumption'.
Abort.

(** Instead, we can write an Ltac1 wrapper for [myassumption].  *)
Ltac myassumption := ltac2:(myassumption).

Goal forall (A B : Prop), A -> B -> A.
  intros.
  myassumption.
Qed.

(** We can also expose functions/data from Ltac1 to Ltac2, though the wrapper would become more complicated as we would need to convert from an untyped language to a statically typed language. The reader can
 refer to the #<a href="https://rocq-prover.org/doc/V9.0.0/refman/proof-engine/ltac2.html##compatibility-layer-with-ltac1">reference manual</a> for details. *)


(** Finally, I want to point out that the [myassumption'] function is defined in a way to showcase
 the strength of Ltac2 as an ML-family language where you can make full use of your functional
  programming knowledge. An alternative (and perhaps easier) way is to use the special
 [lazy_match! goal with] form. *)

Ltac2 myassumption'' () :=
  Control.refine (fun _ =>
                    lazy_match! goal with
                    | [h : ?a |- ?a] =>
                        Control.hyp h
                    end).

(** By picking the same variable [?a] for both the premise (before the [|-]) and the goal (after the [|-]),
 we ensure that the identifier [h] has a type that matches the goal. *)

Ltac myassumption'' := ltac2:(myassumption'' ()).

Goal forall (A B : Prop), A -> B -> A.
  intros.
  myassumption''.
Qed.

(** *** Sequencing Tactics  *)
(** Similar to Ltac, Ltac2 uses the semicolon operator to sequentially run two tactics.
  An idiomatic use of semicolon in Ltac involves running one tactic such as [destruct] followed by
  another tactic to discharge multiple subgoals at once. *)
Goal forall b, b = negb (negb  b).
  destruct b; reflexivity.
Qed.

(** Here, note that [destruct b; reflexivity] is not just calling  [destruct b] and [reflexivity]
    in sequence.
    After generating multiple subgoals with [destruct b], there's the action of focusing on each
    generated subgoals and calling [reflexivity] on each individual goal.  *)

(** In Ltac and Ltac2, the semicolon can be viewed as having the same semantics as the semicolon
from ML, which does nothing
 beyond sequentially chaining two computations. Thus, it is the responsibility of the second
 tactic to decide how it wants to handle multiple goals. The [lazy_match!] construct, for example,
 would simply fail if it directly follows a semicolon with multiple subgoals, unlike its Ltac1 counterpart,
which focuses on the subgoals on its own. *)


(** For example, consider the following alternative definition of [myassumption''], which
 performs the pattern matching before the call to [Control.refine] *)
Ltac2 p_assumption () :=
  lazy_match! goal with
  | [h : ?a |- ?a] =>
      Control.refine (fun _ => Control.hyp h)
  end.

Goal forall A, (A \/ A) -> A.
  intros A h.
  Fail destruct h; ltac2:(p_assumption ()).
  (* Fails because the ltac2 [lazy_match!] doesn't focus the goals on its own *)
  destruct h; lazymatch goal with
         | [h : ?a |- ?a] => apply h
         end.
  (* Works because [lazymatch] focuses each of the subgoals *)
Abort.

(** For the example above, focusing on the subgoals might appear to be a more sensible default,
 however, there are cases where we know in advance that no subgoals will be generated, or
 we are only interested in running the tactic on specific goals. Thus, Ltac2 gives the choice
 to the user to decide which behavior is desired. We'll how we can make use of the flexibility
 shortly. *)

(** For now, to recover the Ltac1 behavior, we wrap our tactic with [Control.enter], which focuses on the
 subgoals generated by the previous tactic. *)

Goal forall A, (A \/ A) -> A.
  intros A h.
  destruct h; ltac2:(Control.enter p_assumption).
  Restart.
  (** Note that [myassumption''] works without [Control.enter], because [Control.refine] knows how
   to handle an unfocused proof state. *)
  intros A h.
  destruct h; myassumption''.
Qed.

(** An alternative to focusing on the subgoals one by one is to focus on one specific subgoal.
 The following [runfirst] tactic uses the [Control.focus] function to focus on the first goal
 and execute the tactic it takes as an argument. *)

Ltac2 runfirst tac : unit := Control.focus 1 1 tac.

Goal forall A B , A \/ (A /\ B) -> A.
  intros A B h.
  destruct h; ltac2:(runfirst p_assumption).
  destruct H. ltac2:(p_assumption ()).
Qed.

(** What [Control.focus i j tac] does is focusing on the [i] through [j]th subgoals before running [tac].
By instantiating both [i] and [j] to 1, we focus only on the very first goal so the [p_assumption]
 tactic successfully discharges the first subgoal but leaves the second one alone. *)


(** *** Basic Exception Handling  *)
(** Thus far, we have been sloppy with the error handling of our programs. In the definition of
 [myassumption'], for example, if no matching hypothesis can be found, one of those API calls/matches
 that interact with the proof state would fail and the user of our tactic is directly exposed
 to the internal exceptions that are hard to parse. *)

(** To provide more useful information to the user of the tactics (which might very well be yourself!),
Ltac2 provides a very sophisticated system for exception handling and backtracking. Here, we consider
 only two functions: [Control.zero] and [Control.plus], which roughly correspond to throw and catch from
 languages like Java. *)

(** Consider the following [get_elem] function, which returns the root element of a tree if it's non-empty,
 but throws a [No_value] exception with [Control.zero] otherwise. *)
Ltac2 Check Control.zero.

Ltac2 get_elem (t : 'a tree) :=
  match t with
  | Node a _ _ => a
  | Empty => Control.zero No_value
  end.

(** Running [get_elem Empty] would give us the expected exception  *)
Fail Ltac2 Eval get_elem Empty.

(** Any exceptions thrown by [Control.zero] is catchable using [Control.plus]. Here's how we
 define a function that tries to call [get_elem] and returns a default argument when an exception
 is thrown. *)

Ltac2 Check Control.plus.

Ltac2 get_elem_def (t : 'a tree) (e : 'a) :=
  Control.plus (fun _ => get_elem t)
    (fun _ => e).

Ltac2 Eval get_elem_def Empty 4.
Ltac2 Eval get_elem_def (Node 5 Empty Empty) 4.

(** For exceptions that are catastrophic and are not meant to be caught, you can use
 [Control.throw]. *)

Ltac2 get_elem' (t : 'a tree) :=
  match t with
  | Node a _ _ => a
  | Empty => Control.throw No_value
  end.

Fail Ltac2 Eval Control.plus (fun _ => get_elem' Empty) (fun _ => 4).
(* Inlining [get_elem_def] just for a side-by-side comparison *)
Ltac2 Eval Control.plus (fun _ => get_elem Empty) (fun _ => 4).


(** *** Bonus: Advanced FFI for handling tacticals   *)

(** What's sometimes referred to as tacticals in Ltac1 are simply unit valued functions in Ltac2.
One can think of tacticals as nothing more than tactics that may take other tactics as inputs.
 One such example is the [runfirst] function we have defined earlier. In this section, we
 discuss how we can use notations on tacticals and export them to Ltac1. *)

(** TODO   *)
