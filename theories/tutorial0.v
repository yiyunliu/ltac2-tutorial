(** * Ltac2 Tutorial: Programming basics and proof state manipulation *)

(** Ltac2 is a new language for writing tactics in Coq. The rationale for the new tactic language
can be found in #<a href="https://coq.inria.fr/doc/V8.18.0/refman/proof-engine/ltac2.html">the Coq
documentation</a>#. As of late, the use of Ltac1 is #<a href="https://coq.inria.fr/doc/V8.18.0/refman/proof-engine/ltac.html">discouraged</a>#,
though there are still plenty of tactics written in Ltac1 that have not been ported to Ltac2 (e.g. ssreflect).


However, thanks to the convenient interfacing between Ltac1 and Ltac2, it is already possible to use Ltac2
to write complex logic and export it for use in Ltac1. Compared to Ltac1, I find Ltac2 much easier to learn,
due to its much more sane treatment of metaprogramming where the metaprograms (i.e. Ltac2 expressions) and
the object programs (i.e. Gallina terms) are cleanly separated.


Furthermore, compared to Ltac1, Ltac2 is much more
expressive, with many useful features from ML-family languages, including algebraic data types, record types,
pattern matching. Tactics are no longer special and are treated as effectual thunks that manipulate the proof
state.

Ltac2 comes with the Coq installation if your version number is recent enough.
The tutorial was written using Coq 8.18.0, though an earlier version might also work for stepping through
the examples. *)

(** ** Proof mode and namespace *)
(** Before we start the tutorial, we first import the necessary file that would allow us to use Ltac2.  *)
From Ltac2 Require Import Ltac2.

(** The command above not only makes Ltac2 available, but also sets the Proof Mode of the proof scripts to
 "Ltac2" mode. This means we can only use
 #<a href="https://github.com/coq/coq/blob/master/user-contrib/Ltac2/Notations.v">
tactics defined in Ltac2</a>#. *)

Goal forall (A : Prop), A -> A.
Proof.
  intros A h.
  exact h.
Qed.

(** [intros A h] and [exact h] both work since they are defined in the Ltac2 standard library. *)

Goal forall (A : Prop), A -> A.
Proof.
  Fail tauto.
Abort.

(** [tauto] fails since it is not defined in Ltac2. To invoke Ltac1 tactics, we need to wrap the tactics
inside [ltac1:(..)] *)
Goal forall (A : Prop), A -> A.
Proof.
  ltac1:(tauto).
Qed.

(** We can also encapsulate the foreign function call to Ltac1 inside an Ltac2
wrapper function *)
Ltac2 tauto () := ltac1:(tauto).
(** Note that the [tauto] definition from above is not recursive.
The [Ltac2 tauto] declaration creates a function named [tauto] in
the Ltac2 namespace, which is disjoint from that of Ltac1. The [tauto] in the
RHS of the definition, wrapped in [ltac1:(..)], refers to the [tauto] from
he Ltac1 namespace. *)

Ltac2 Eval tauto.
(** The [tauto] tactic we just defined has the signature [unit -> unit].
Its output is not interesting and we only care about its effect on the proof
state when we evaluate it by passing in a trivial unit argument. As the
following example shows. *)
Goal forall (A : Prop), A -> A.
Proof.
  tauto ().
Qed.

(** Having to pass [tauto] a unit value [()] is awkward and is not
 something we are used to. This is reconciled by the use of notations. *)
Ltac2 Notation "tauto" := tauto ().
(** Now we can invoke tauto directly without passing it the unit argument explicitly. *)
Goal forall (A : Prop), A -> A.
Proof.
  tauto.
Qed.

(** ** Arithmetic expressions *)
(** Interactively writing and evaluating expressions is the best way to
 understand how a programming language works. In this section, we show
 how to write basic arithmetic expressions and functions in Ltac2. Let's
 start with integer literals and the addition function. *)
Ltac2 Eval 1.
Ltac2 Eval Int.add 1 2.
(** [Ltac2 Eval] is a vernacular command that evaluates an Ltac2 expression.
 In the example above, the integer [1] evaluates to itself, and the
expression [Int.add 1 2] reduces to the integer [3]. It is important to
 understand that the numbers appearing on the rhs are Ltac2 expressions, not
 Gallina expressions. The [int] type is a primitive type in Ltac2, and
 has nothing to do with integers from the Coq standard library. *)
Definition double_num (a : nat) := a + a.
Fail Ltac2 Eval double_num 4.
(** Note how Coq compalins about myfunc being an unbound value in the example above *)

(** As per standard for ML-family languages, Ltac2 supports higher order
functions. With Hindley-Milner style type inference, we can define the
 polymorphic identity function as follows without any type annotations. *)
Ltac2 Eval (fun x => x).

(** We can evaluate a function immediately by passing it an argument.  *)
Ltac2 Eval (fun x => Int.add x x) 4.

(** Ltac2 also supports let bindings. Here's the previous example where the
 funciton is bound to the variable [f]. *)
Ltac2 Eval let f := fun x => Int.add x x in f 4.

(** The following command defines the doubling function as a top-level function
 named [double_num]. *)
Ltac2 double_num := fun x => Int.add x x.

(** Here's the usual shorthand that avoids the anonymous lambda. *)
Ltac2 double_num' x := Int.add x x.

(** We can add type annotations to Ltac2 expressions. *)
Ltac2 double_num'' (x : int) := Int.add x x.

Ltac2 Eval double_num 4.

(** The [Ltac2.Int] module provides helpful functions that we can reuse.
The standard library is sadly not well-documented and you really have to
read the source code. For example, #<a href="https://github.com/coq/coq/blob/master/user-contrib/Ltac2/Int.v">here's the file</a>#
where you can find other functions from the [Ltac2.Int] module. *)
Ltac2 is_even x := Int.equal (Int.mod x 2) 0.


(** By adding the [rec] modifier to our definition, we can write recursive
 functions. Unlike Gallina, there's no termination checker. You are free
 to use general recursion. *)
Ltac2 rec collatz n :=
  if Int.le n 1
  then 0
  else
    if is_even n
    then Int.add 1 (collatz (Int.div n 2))
    else Int.add 1 (collatz (Int.add 1 (Int.mul 3 n))).

Ltac2 Eval collatz 481902482190480.

(** ** Algebraic data types *)
(** One of my favorite things about Ltac2 is support for algebraic data types.
 It really adds a lot of flexibility when you write sophisticated search
 algorithms that requires real data structures. *)

(** Let's start with a simple recursive data type: peano numbers. *)
Ltac2 Type rec PNat :=
  [ Z | S (PNat) ].

(** We can define the addition operation for [PNat]. *)
Ltac2 rec padd (m : PNat) (n : PNat) :=
  match m with
  | Z => n
  | S m => S (padd m n)
  end.

Ltac2 Eval padd (S (S Z)) (S Z).
(** The result of evaluation should not be surprising. *)

(** We can also define data types with type parameters. These are useful for
 defining container types.*)
Ltac2 Type rec 'a Tree :=
  [ Empty | Node ('a, 'a Tree, 'a Tree)].

(** Pay attention to the [Node] constructor. It shows you how to include
multiple fields in one constructor. *)

Ltac2 rec tree_size (t : 'a Tree) :=
  match t with
  | Empty => 0
  | Node _ l r => Int.add 1 (Int.add (tree_size l) (tree_size r))
  end.

Ltac2 Eval tree_size (Node 1 (Node 2 Empty Empty) Empty).

(** ** Record types *)
Ltac2 Type ('a, 'b) Pair := { fst : 'a ; snd : 'b }.

Ltac2 Eval { fst := 1 ; snd := 2 }.

(** The parentheses are necessary for projecting out individual fields  *)
Ltac2 Eval { fst := 1 ; snd := "2" }.(fst).
Ltac2 Eval let p := { fst := 1 ; snd := "2" } in p.(snd).

(** ** Constructing Gallina terms *)
(** To construct a Gallina term, we want to quote it with ' *)
Ltac2 Eval '1.
(** [constr] is a type that represents a Gallina term. *)
Ltac2 Eval '(1 + 1).

(** Of course, we can refer to Gallina top-level definitions. *)
Definition four := 4.
Ltac2 Eval 'four.

(** Note that quoting is effectual because quoting triggers type checking.
 The following Ltac2 expressions result in failure because of undefined
 identifiers or Gallina type errors  *)
Fail Ltac2 Eval 'five.
Fail Ltac2 Eval '(1 + nil).

(** Inside a quote, we can refer to Ltac2 variables using $ *)
(** If you are familiar with lisp, think of ' as `
   $ as , that only works with variables *)
Ltac2 rec int_n n :=
  if Int.le n 0
  then '0
  else let m := int_n (Int.sub n 1) in
       '(1 + $m).

(**  [int_n n] creates the Gallina expression [(1 + (1 + (1 + ... + 0)))]
 where [1] appears [n] times. *)
Ltac2 Eval int_n 4.

(** We can use Constr.equal to test the syntactic equality (up to
   alpha-equivalence) of Gallina terms. *)
Ltac2 Eval Constr.equal '(fun x : nat => x) '(fun z : nat => z).

(** On the other hand, 1 + 1 and 2 are syntactically distinct terms. *)
Ltac2 Eval Constr.equal '(1 + 1) '2.

(** We can use different eval algorithms to evaluate terms
(see #<a href="https://github.com/coq/coq/blob/master/user-contrib/Ltac2/Std.v">the Ltac2 source</a># for different variants). *)
Ltac2 Eval Std.eval_vm None '(1 + 1).
Ltac2 Eval Std.eval_vm None '((fun x => x * x) 100).
Ltac2 Eval Std.eval_hnf '((fun x => x * x) 100).
(** Reducing an ill-typed term results in an error. *)
Fail Ltac2 Eval Std.eval_hnf '(1 + (fun x => x + x)).

(** ** Manipulating proof state *)
(** Ltac2 is impure. Apart from mutable cells, it's possible to query
and mutate the proof state. We have already seen this earlier with constructing
 Gallina terms. If a Gallina term we are about to construct is ill-formed,
 Ltac2 runtime raises an error. *)

(** First, let's see how we can query the proof state.
 The built-in function hyps give us a list of hypotheses in the
   proof context. We can use it to build a tactic that works like
   the [assumption] tactic. *)
Ltac2 Eval Control.hyps.
(* Control.hyps : unit -> (ident * constr option * constr) list *)
(** [Control.hyps] returns the hypotheses as a list of [(hyp-name, definition, type)].
   [list] is a data structure defined in the Ltac2 standard library.
   You can find its related utility functions in the Ltac2.List module *)

(** Control.hyps needs to be a function because Ltac2 is a
   call-by-value language and a variable of type [... list] would be a
   constant that cannot cause any effect when evaluated *)

(** The built-in function goal returns a gallina term that represents
   the goal. *)
Ltac2 Eval Control.goal.
(* Control.goal : unit -> constr = <fun> *)

Lemma ex1 : 1 = 2 -> 1 = 2.
Proof.
  intro H.
  pose (4 : id nat) as n.

  Ltac2 Eval Control.hyps ().
  (* (@H, None, constr:(1 = 2)); *)
  (* (@n, Some (constr:(4)), constr:(id nat)) *)

  Ltac2 Eval Control.goal ().
  (* constr:(1 = 2) *)

  (** We can use the List.find from the standard library to look for an
     element from the list that we are interested in *)
  Ltac2 Eval List.find (fun (_,_,ty) => Constr.equal (Std.eval_vm None ty) 'nat) (Control.hyps ()).
  (* (@n, Some (constr:(4 : id nat)), constr:(id nat)) *)

  (** A direct comparison without Std.eval_vm would result in failure since id nat is not syntactically equal to nat *)
  Fail Ltac2 Eval List.find (fun (_,_,ty) => Constr.equal ty 'nat) (Control.hyps ()).
Abort.

(** ** Our first tactic **)
(** We will define [find_assumption], a tactic that finds a hypothesis that matches the goal.
In general, [Ltac2 foo () := ...] defines a function that takes
   a unit as its first argument.
 *)
Ltac2 find_assumption () : constr :=
  let g := Control.goal () in
  let h := List.find (fun (_,_,ty) => Constr.equal g ty) (Control.hyps ()) in
  match h with
  | (h_ident, _, _) => Control.hyp h_ident
  end.
(** Note that [h_ident] is an identifier. We need to use [Control.hyp] to resolve it into a Gallina term. *)


Lemma ex2 : 1 = 2 -> 1 = 2.
Proof.
  intro H.
  Ltac2 Eval find_assumption ().

  (** [find_assumption ()] will find H as the hypothesis matching our goal.
   So far, we have only queried the proof state, but we haven't
     really changed it.

  One way to change the proof state is to simply finish the proof
   [Control.refine] takes a computation that returns a Gallina term
     and use that Gallina term to complete the goal. [Control.refine]
     returns unit because its meant to mutate the proof state. *)
  Control.refine find_assumption.
  (** Now the goal is completed *)
Qed.

(** We can now implement our own assumption tactic as follows: *)
Ltac2 my_assumption () :=
  Control.refine find_assumption.

Lemma id_prop (A : Prop) : A -> A.
Proof.
  intro H.
  my_assumption ().
Qed.

(** Again, we can use notations to avoid the parentheses when invoking the thunk. *)
Ltac2 Notation "my_assumption" := my_assumption ().

Lemma id_prop' (A : Prop) : A -> A.
Proof.
  intro H.
  my_assumption.
Qed.


(** ** Extra: More on constr  *)
(** [constr] is an opaque type so we can't directly pattern match on it
   as if it is an algebraic data type. Instead, we must use special
   [match!] and [lazy_match!] forms. *)

Ltac2 rec mirror_plus (tm : constr) :=
  lazy_match! tm with
  | ?a + ?b =>
      let rev_b := mirror_plus b in
      let rev_a := mirror_plus a in
      '($rev_b + $rev_a)
  (** [rev_b] and [rev_a] are Ltac2 variables representing Gallina terms.

We need to use antiquote to refer to these metavariables
         within a Gallina term *)
  | _ => tm
  end.

Ltac2 Eval mirror_plus '(1 + 2 + 3).

(** Just like in Ltac1, we can also match the entire proof context.
   As an example, we define an alternative version of [my_assumption]. *)
Ltac2 my_assumption' () :=
  (** goal is not a variable. lazy_match! goal with is its own syntactic form *)
  lazy_match! goal with
  (** match! goal with would also work *)
  | [ h_ident : ?a |- ?a ] =>
      (** Again, h_ident is of type identifier. We need to use
         Control.hyp to perform a lookup in the proof context and
         produce a Gallina term *)
      let h := Control.hyp h_ident in
      Control.refine (fun _ => h)
  end.

Goal forall A, A -> A.
Proof.
  intros.
  my_assumption' ().
Qed.

(** However, my_assumption' doesn't work as expected when we put it
   behind a semicolon to discharge multiple goals. *)
Goal forall A, A \/ A -> A.
Proof.
  Fail (intros A [? | ?]; my_assumption' ()).
  (** The reason is that Ltac2 doesn't always focus on the individual
     goals automatically when multiple goals are produced by the
     previous tactic. We need to use Control.enter to explicitly focus
     on each individaul goals *)
  Ltac2 Eval Control.enter.

  intros A [? | ?]; Control.enter my_assumption'.
Qed.

(** We can now wrap my_assumption' inside a notation. *)
Ltac2 Notation "my_assumption'" := Control.enter my_assumption'.

Goal forall A, A \/ A -> A.
Proof.
  intros A [? | ?]; my_assumption'.
Qed.

(** ** Bonus: Traverse the Gallina AST explicitly *)
(** Constr.Unsafe.kind turns a constr into an exported algebraic data type
   kind that you can match against. However, it is unsafe because you can
   easily end up with open terms.

TODO
 *)
