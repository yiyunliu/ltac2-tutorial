From Ltac2 Require Import Ltac2.
From Coq Require Import List.

(* This file shows how to do proof by reflection with Ltac2, *)
(* See http://adam.chlipala.net/cpdt/html/Cpdt.Reflection.html for a more detailed explanation of the high-level idea *)
Module Type Monoid.

  (* Carrier *)
  Parameter M : Type.

  (* Neutral element *)
  Parameter mzero : M.

  (* Binary operator *)
  Parameter madd : M -> M -> M.

  (* Axioms *)
  Axiom madd_assoc : forall a b c, madd (madd a b) c = madd a (madd b c).

  Axiom madd_idl : forall a, madd mzero a = a.

  Axiom madd_idr : forall a, madd a mzero = a.

End Monoid.

Module MonoidSimp (M : Monoid).
  Import M.
  Inductive mexp  : Type :=
  | Id : mexp
  | Var : M -> mexp
  | Op : mexp -> mexp -> mexp.

  Fixpoint denote_mexp (e : mexp) :=
    match e with
    | Id => mzero
    | Var a => a
    | Op a b => madd (denote_mexp a) (denote_mexp b)
    end.

  Definition denote_mexps :=
    fold_right madd mzero.

  Fixpoint flatten (e : mexp) :=
    match e with
    | Id => nil
    | Var a => cons a nil
    | Op e0 e1 => flatten e0 ++ flatten e1
    end.

  Lemma denote_append L1 L2 :
    denote_mexps (L1 ++ L2) = madd (denote_mexps L1) (denote_mexps L2).
  Proof.
    revert L2.
    induction L1 as [|m L1 ihL1].
    - simpl. intros L2.
      rewrite madd_idl.
      reflexivity.
    - intros L2. simpl.
      rewrite ihL1.
      rewrite madd_assoc.
      reflexivity.
  Qed.

  Lemma flatten_correct (e : mexp) :
    denote_mexp e = denote_mexps (flatten e).
  Proof.
    induction e; simpl.
    - reflexivity.
    - rewrite madd_idr. reflexivity.
    - rewrite denote_append.
      rewrite IHe1.
      rewrite IHe2.
      reflexivity.
  Qed.

  (* To show that two expressions are equal, it suffices to show that their simplified versions are equal *)
  Lemma monoid_reflect (e0 e1 : mexp) :
    denote_mexps (flatten e0) = denote_mexps (flatten e1) ->
    denote_mexp e0 = denote_mexp e1.
  Proof.
    do 2 (rewrite flatten_correct).
    apply id.
  Qed.

  (* Convert a Gallina expression as a term of the type mexp *)
  Ltac2 rec reify a :=
    lazy_match! a with
    | mzero => 'Id
    | madd ?a ?b  =>
        let e0 := reify a in
        let e1 := reify b in
        '(Op $e0 $e1)
    | _ => '(Var $a)
    end.

  (* Apply monoid_reflect and simplify the result for a goal of the
  form a = b where a and b are both of type M *)
  Ltac2 rec simp_monoid () :=
    lazy_match! goal with
    | [ |- ?a = ?b] =>
        let m0 := reify a in
        let m1 := reify b in
        change (denote_mexp $m0 = denote_mexp $m1);
        apply monoid_reflect;
        simpl
    | [ |- _] => Control.backtrack_tactic_failure "Wrong goal type"
    end.

End MonoidSimp.


(* Now let's try out our new simplifier *)
Module MonoidNat <: Monoid.

  Definition M := nat.

  (* Neutral element *)
  Definition mzero := 0.

  (* Binary operator *)
  Definition madd := Nat.add.

  (* Axioms *)
  Lemma madd_assoc : forall a b c, madd (madd a b) c = madd a (madd b c).
  Proof.
    unfold madd. intros a b c.
    rewrite PeanoNat.Nat.add_assoc.
    reflexivity.
  Qed.

  Lemma madd_idl : forall a, madd mzero a = a.
  Proof.
    apply PeanoNat.Nat.add_0_l.
  Qed.

  Lemma madd_idr : forall a, madd a mzero = a.
  Proof.
    apply PeanoNat.Nat.add_0_r.
  Qed.
End MonoidNat.

Module MonoidNatSimp := MonoidSimp (MonoidNat).

Import MonoidNat.
Import MonoidNatSimp.

Goal forall (a b c d : M), madd a (madd (madd b c) d) = madd (madd a b) (madd c d).
  intros a b c d.
  simp_monoid ().
  reflexivity.
Qed.
