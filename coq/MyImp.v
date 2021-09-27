(** * Imp: Simple Imperative Programs *)

(** "One man's code is another man's data."
    (Alan Perlis) *)

(** In this chapter, we take a more serious look at how to use Coq to
    study other things.  Our case study is a _simple imperative
    programming language_ called Imp, embodying a tiny core fragment
    of conventional mainstream languages such as C and Java.  Here is
    a familiar mathematical function written in Imp.

       Z := X;
       Y := 1;
       while ~(Z = 0) do
         Y := Y * Z;
         Z := Z - 1
       end
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.

(* ################################################################# *)
(** * Arithmetic and Boolean Expressions *)

(** We'll present Imp in three parts: first a core language of
    _arithmetic and boolean expressions_, then an extension of these
    expressions with _variables_, and finally a language of _commands_
    including assignment, conditions, sequencing, and loops. *)

(* ================================================================= *)
(** ** Syntax *)

Module AExp.

(** These two definitions specify the _abstract syntax_ of
    arithmetic and boolean expressions. *)

(* We want to define four kinds of arithmetic expressions:
    + Natural Numbers
    + Additions
    + Subtractions
    + Multiplications *)

Inductive aexp : Type :=
  | ANum (n:nat)
  | APlus (a:aexp) (b:aexp)
  | AMinus (a:aexp) (b:aexp)
  | AMult (a:aexp) (b:aexp).

(* 1+2*3 --> concrete syntax *)
(* APlus (ANum 1) (AMult (ANum 2) (ANum 3)) --> Abstract syntax*)  

(* Boolean expressions:
    + Booleans - true and false
    + Equalities and inequalities of arithmetic expressions
    + Negation and Conjunction*)
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a:aexp) (b:aexp) (* a =b*)
  | BLe (a:aexp) (b:aexp) (* a <= b *)
  | BNot (a:bexp)
  | BAnd (a:bexp) (b:bexp). 

(** AST of ["1 + 2 * 3"] is
      APlus (ANum 1) (AMult (ANum 2) (ANum 3)).
*)






(** For comparison, here's a conventional BNF (Backus-Naur Form)
    grammar defining the same abstract syntax:

    a := nat
        | a + a
        | a - a
        | a * a

    b := true
        | false
        | a = a
        | a <= a
        | ~ b
        | b && b
*)


(* ================================================================= *)
(** ** Evaluation *)

(** _Evaluating_ an arithmetic expression produces a number. *)

Fixpoint aeval (a : aexp) : nat := 
  match a with
  | ANum n => n
  | APlus a b => (aeval a) + (aeval b)
  | AMinus a b => (aeval a) - (aeval b)
  | AMult a b => (aeval a) * (aeval b)
  end.

(* 2+2 --> 4*)
Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

(** Similarly, evaluating a boolean expression yields a boolean. *)

Fixpoint beval (b : bexp) : bool := 
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a b => Nat.eqb (aeval a) (aeval b)
  | BLe a b => Nat.leb (aeval a) (aeval b)
  | BNot a => negb (beval a)
  | BAnd a b => andb (beval a) (beval b)
  end.

(* ================================================================= *)
(** ** Optimization *)

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus  e1 e2 => APlus  (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult  e1 e2 => AMult  (optimize_0plus e1) (optimize_0plus e2)
  end.

(** 2 + 0 + 0 + 1 = 2 + 1 *)

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. simpl. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *)  simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. reflexivity.  
Qed.

(* ################################################################# *)
(** * Evaluation as a Relation *)

(** We have presented [aeval] and [beval] as functions defined by
    [Fixpoint]s.  Another way to think about evaluation -- one that we
    will see is often more flexible -- is as a _relation_ between
    expressions and their values.  This leads naturally to [Inductive]
    definitions like the following one for arithmetic expressions... *)

(** For example, [==>] is the smallest relation closed under these
    rules:

                             -----------                               (E_ANum)
                             ANum n ==> n

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_APlus)
                         APlus e1 e2 ==> n1+n2

                               e1 ==> n1
                               e2 ==> n2
                        ---------------------                        (E_AMinus)
                        AMinus e1 e2 ==> n1-n2

                               e1 ==> n1
                               e2 ==> n2
                         --------------------                         (E_AMult)
                         AMult e1 e2 ==> n1*n2
*)

Module aevalR_first_try.

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      aevalR (ANum n) n
  | E_APlus: forall (e1 e2 : aexp) (n1 n2 : nat),
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

(** It will be convenient to have an infix notation for
    [aevalR].  We'll write [e ==> n] to mean that arithmetic expression
    [e] evaluates to value [n]. *)

Notation "e '==>' n"
         := (aevalR e n)
            (at level 90, left associativity)
         : type_scope.

End aevalR_first_try.

Reserved Notation "e '==>' n" (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (APlus e1 e2)  ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 ==> n1) -> (e2 ==> n2) -> (AMult e1 e2)  ==> (n1 * n2)

  where "e '==>' n" := (aevalR e n) : type_scope.


(* ================================================================= *)
(** ** Equivalence of the Definitions *)

(** It is straightforward to prove that the relational and functional
    definitions of evaluation agree: *)

Theorem aeval_iff_aevalR : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  {
    intros H. induction H.
    + simpl. reflexivity.
    + simpl. rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + simpl. rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + simpl. rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.    
  }
  {
    generalize dependent n. induction a.
    + simpl. intros. subst. apply E_ANum.
    + simpl. intros. subst. apply E_APlus.
      - apply IHa1. reflexivity.
      - apply IHa2. reflexivity.
    + simpl. intros. subst. apply E_AMinus.
      - apply IHa1. reflexivity.
      - apply IHa2. reflexivity.
    + simpl. intros. subst. apply E_AMult.
    - apply IHa1. reflexivity.
    - apply IHa2. reflexivity.      
  }
Qed.

Theorem aeval_iff_aevalR' : forall a n,
  (a ==> n) <-> aeval a = n.
Proof.
  split.
  {
    intros H. induction H; simpl; try rewrite IHaevalR1; try rewrite IHaevalR2; reflexivity.
  }
  {
    generalize dependent n. induction a; simpl; intros; subst; constructor;
    try apply IHa1; try apply IHa2; reflexivity.
  }
Qed.


(* ================================================================= *)
(** ** Computational vs. Relational Definitions *)

Module aevalR_division.

(** For example, suppose that we wanted to extend the arithmetic
    operations with division: *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).         (* <--- NEW *)

(** Extending the definition of [aeval] to handle this new
    operation would not be straightforward (what should we return as
    the result of [ADiv (ANum 5) (ANum 0)]?).  But extending [aevalR]
    is very easy. *)

Reserved Notation "e '==>' n"
                  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) :
      (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (AMult a1 a2) ==> (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :          (* <----- NEW *)
      

where "a '==>' n" := (aevalR a n) : type_scope.

(** Notice that the evaluation relation has now become _partial_:
    There are some inputs for which it simply does not specify an
    output. *)

End aevalR_division.

Module aevalR_extended.