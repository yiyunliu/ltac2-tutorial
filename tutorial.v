From Ltac2 Require Import Ltac2.

(* Simple expressions *)
(* Note that int is not a data type available in Gallina *)
(* It is primitive data type in Ltac2 *)
Ltac2 Eval 1.

Ltac2 Eval Int.add 1 2.

(* Lambdas *)
Ltac2 Eval (fun x => x).

(* See https://github.com/coq/coq/blob/master/user-contrib/Ltac2/ for
   the Ltac2 standard library functions *)
Ltac2 Eval (fun x => Int.add x x) 4.

(* Let bindings *)
Ltac2 Eval let f := fun x => Int.add x x in f 4.

(* Top-level functions *)
Ltac2 double_int := fun x => Int.add x x.

(* A syntax sugar of the former *)
Ltac2 double_int' x := Int.add x x.

(* We can add annotations to our types *)
Ltac2 double_int'' (x : int) := Int.add x x.

Ltac2 Eval double_int 4.

Ltac2 is_even x := Int.equal (Int.mod x 2) 0.

(* Recursive functions *)
Ltac2 rec collatz n :=
  if Int.le n 1
  then 0
  else
    (* if is_even x *)
    if is_even n
    then Int.add 1 (collatz (Int.div n 2))
    else Int.add 1 (collatz (Int.add 1 (Int.mul 3 n))).

Ltac2 Eval collatz 10.

(* Algebraic data types *)
Ltac2 Type rec PNat :=
  [ Z | S (PNat) ].

Ltac2 rec padd (m : PNat) (n : PNat) :=
  match m with
  | Z => n
  | S m => S (padd m n)
  end.

Ltac2 Eval padd (S (S Z)) (S Z).

(* Type parameters *)
Ltac2 Type rec 'a Tree :=
  [ Empty | Node ('a, 'a Tree, 'a Tree)].

Ltac2 rec tree_size (t : 'a Tree) :=
  match t with
  | Empty => 0
  | Node _ l r => Int.add 1 (Int.add (tree_size l) (tree_size r))
  end.

Ltac2 Eval tree_size (Node 1 (Node 2 Empty Empty) Empty).

(* Records *)
Ltac2 Type ('a, 'b) Pair := { fst : 'a ; snd : 'b }.

Ltac2 Eval { fst := 1 ; snd := 2 }.

(* Projecting out a record *)
Ltac2 Eval { fst := 1 ; snd := "2" }.(fst).

Ltac2 Eval let p := { fst := 1 ; snd := "2" } in p.(snd).

(* Constructing Gallina terms *)
(* To construct a Gallina term, we want to quote it with ' *)
Ltac2 Eval '1.
(* constr is a type that represents a Gallina term *)

Ltac2 Eval '(1 + 1).

(* Of course, we can refer to Gallina top-level definitions *)
Definition four := 4.

Ltac2 Eval 'four.

(* Ltac2 Eval four. *)

(* Ltac2 Eval 'five. *)

(* int_n 3 ~> (1 + (1 + (1 + 0))) *)
(* int_n 0 ~> 0 *)

(* Inside a quote, we can refer to Ltac2 variables using $ *)
(* If you are familiar with lisp, think of ' as `
   $ as , that only works with variables *)
Ltac2 rec int_n n :=
  if Int.le n 0
  then '0
  else let m := int_n (Int.sub n 1) in
       '(1 + $m).

Ltac2 Eval int_n 4.

(* We can use Constr.equal to test the syntactic equality (up to
   alpha-equivalence) of Gallina terms *)
Ltac2 Eval Constr.equal '(fun x : nat => x) '(fun z : nat => z).

(* Ltac2 is impure. Apart from mutable cells, it's possible to query
and mutate the proof state *)

(* First, let's see how we can query the proof state *)

(* The built-in function hyps give us a list of hypotheses in the
   proof context. We can use it to build a tactic that works like
   assumption *)
Ltac2 Eval Control.hyps.
(* Control.hyps : unit -> (ident * constr option * constr) list *)
(* Return the hypotheses as a list of (hyp-name, definition, type).
   list is a data structure defined in the Ltac2 standard library.
   You can find its related utility functions in the Ltac2.List module *)
(* Control.hyps needs to be a function because Ltac2 is a
   call-by-value language and a variable of type ... list would be a
   constant *)

(* The built-in function goal returns a gallina term that represents
   the goal *)
Ltac2 Eval Control.goal.
(* Control.goal : unit -> constr = <fun> *)

Lemma ex1 : 1 = 2 -> 1 = 2.
Proof.
  intro H.
  pose 4.

  Ltac2 Eval Control.hyps ().
  (* (@H, None, constr:(1 = 2)); *)
  (* (@n, Some (constr:(4)), constr:(nat)) *)

  Ltac2 Eval Control.goal ().
  (* constr:(1 = 2) *)

  (* We can use the List.find from the standard library to look for an
     element from the list that we are interested in *)
  Ltac2 Eval List.find (fun (_,_,ty) => Constr.equal ty 'nat) (Control.hyps ()).
  (* (@n, Some (constr:(4)), constr:(nat)) *)
Abort.

(* find_assumption finds a hypothesis that matches the goal *)
(* In general, Ltac2 foo () := ... defines a function that takes
   a unit as its first argument *)
Ltac2 find_assumption () : constr :=
  let g := Control.goal () in
  let h := List.find (fun (_,_,ty) => Constr.equal g ty) (Control.hyps ()) in
  match h with
  (* h_ident is an identifier. We need to use Control.hyp to turn it
     into a Gallina term *)
  | (h_ident, _, _) => Control.hyp h_ident
  end.

Lemma ex2 : 1 = 2 -> 1 = 2.
Proof.
  intro H.
  Ltac2 Eval find_assumption ().

  (* find_assumption () will find H as the hypothesis matching our goal *)
  (* So far, we have only queried the proof state, but we haven't
     really changed it *)
  (* One way to change the proof state is to simply finish the proof *)
  (* Control.refine takes a computation that returns a Gallina term
     and use that Gallina term to complete the goal. Control.refine
     returns unit because its meant to mutate the proof state. *)
  Control.refine find_assumption.
  (* Now the goal is completed *)
Qed.

(* We can now implement our own assumption tactic as follows: *)
Ltac2 my_assumption () :=
  Control.refine find_assumption.

Lemma id_prop (A : Prop) : A -> A.
Proof.
  intro H.
  my_assumption ().
Qed.

(* Our tactic looks odd since we always need to explicitly add ()
   after it. *)
(* To use your Ltac2 tactic in your proof script, you want to create a
   notation for it so you don't have to type in the () each time *)

(* Note that it is not a cyclic definition. The my_assumption on the
   RHS of := is bound to the Ltac2 definition from earlier. *)
Ltac2 Notation "my_assumption" := my_assumption ().

Lemma id_prop' (A : Prop) : A -> A.
Proof.
  intro H.
  my_assumption.
Qed.

(* In fact, the moment you require and import Ltac2 in your coq file,
   all the tactics in your proof script will refer to Ltac2
   tactics/notations by default, including intro and pose we used
   earlier *)
(* https://github.com/coq/coq/blob/master/user-contrib/Ltac2/Notations.v *)
(* The Ltac2 standard library is far from complete. Many tactics
   available in Ltac1 are missing *)
Goal forall P Q, (P -> Q) -> P -> Q.
  Fail tauto.
Abort.

(* We can make foreign call to Ltac1 libraries through ltac1:(..) *)
(* We can reuse the name tauto because Ltac1 and Ltac2 don't share the
   same namespace *)
Ltac2 tauto () := ltac1:(tauto).
(* tauto on the RHS of := refers to the tauto defined in Ltac1 *)
(* Again, it makes no sense to write tauto as a variable of type unit
   in a call-by-value language. We need to define it as a function so
   it can perform some action *)
(* To get rid of the parentheses, we use the same notation trick *)
Ltac2 Notation "tauto" := tauto ().

Goal forall P Q, (P -> Q) -> P -> Q.
  tauto.
Qed.

(* Tactics that take arguments are trickier because if we don't even
   have the type information of how many arguments the Ltac1 tactic
   takes *)

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


(* Extra: More on constr  *)
(* constr is an opaque type so we can't directly pattern match on it
   as if it is an algebraic data type. Instead, we must use special
   match! and lazy_match! forms *)

Ltac2 rec mirror_plus (tm : constr) :=
  lazy_match! tm with
  | ?a + ?b =>
      let rev_b := mirror_plus b in
      let rev_a := mirror_plus a in
      '($rev_b + $rev_a)
      (* rev_b and rev_a are Ltac2 variables representing Gallina terms *)
      (* We need to use antiquote to refer to these metavariables
         within a Gallina term *)
  | _ => tm
  end.

Ltac2 Eval mirror_plus '(1 + 2 + 3).

(* Just like in Ltac1, we can also match the entire proof context.
   As an example, we define an alternative version of my_assumption *)
Ltac2 my_assumption' () :=
  (* goal is not a variable. lazy_match! goal with is its own syntactic form *)
  lazy_match! goal with
  (* match! goal with would also work *)
  | [ h_ident : ?a |- ?a ] =>
      (* Again, h_ident is of type identifier. We need to use
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

(* However, my_assumption' doesn't work as expected when we put it
   behind a semicolon to discharge multiple goals *)
Goal forall A, A \/ A -> A.
Proof.
  Fail (intros A [? | ?]; my_assumption' ()).
  (* The reason is that Ltac2 doesn't always focus on the individual
     goals automatically when multiple goals are produced by the
     previous tactic. We need to use Control.enter to explicitly focus
     on each individaul goals *)
  Ltac2 Eval Control.enter.

  intros A [? | ?]; Control.enter my_assumption'.
Qed.

(* We can now wrap my_assumption' inside a notation *)
Ltac2 Notation "my_assumption'" := Control.enter my_assumption'.

Goal forall A, A \/ A -> A.
Proof.
  intros A [? | ?]; my_assumption'.
Qed.

(* Bonus: Unsafe.kind: traverse the Gallina AST explicitly *)
(* Constr.Unsafe.kind turns a constr into an exported algebraic data type
   kind that you can match against. However, it is unsafe because you can
   easily end up with open terms... *)
