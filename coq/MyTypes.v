(** * Types: Type Systems *)

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of the simplest
    imaginable language, to introduce the basic ideas of types and
    typing rules and the fundamental theorems about type systems:
    _type preservation_ and _progress_.  In chapter [Stlc] we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq!). *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Arith.Arith.
From LF Require Import Maps.
From LF Require Import Imp.
From LF Require Import Smallstep.

Hint Constructors multi : core.

(* ################################################################# *)
(** * Typed Arithmetic & Boolean Expressions *)
(* ================================================================= *)
(** ** Syntax *)

(** Here is the syntax, informally:

    t ::= tru
        | fls
        | test t then t else t
        | zro
        | scc t
        | prd t
        | iszro t

    And here it is formally: *)

Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | test : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm.

(** (Since it is so simple, we will not bother introducing custom
    concrete syntax for this language.) *)

(** _Values_ are [tru], [fls], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_tru : bvalue tru
  | bv_fls : bvalue fls.

Inductive nvalue : tm -> Prop :=
  | nv_zro : nvalue zro
  | nv_scc : forall t, nvalue t -> nvalue (scc t).

Definition value (t : tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue : core.
Hint Unfold value : core.

(* ================================================================= *)
(** ** Operational Semantics *)

(** Here is the single-step relation, first informally...

                   -------------------------------                  (ST_TestTru)
                   test tru then t1 else t2 --> t1

                   -------------------------------                  (ST_TestFls)
                   test fls then t1 else t2 --> t2

                               t1 --> t1'
            ----------------------------------------------------       (ST_Test)
            test t1 then t2 else t3 --> test t1' then t2 else t3

                             t1 --> t1'
                         ------------------                             (ST_Scc)
                         scc t1 --> scc t1'

                           ---------------                           (ST_PrdZro)
                           prd zro --> zro

                         numeric value v
                        -------------------                          (ST_PrdScc)
                        prd (scc v) --> v

                              t1 --> t1'
                         ------------------                             (ST_Prd)
                         prd t1 --> prd t1'

                          -----------------                        (ST_IszroZro)
                          iszro zro --> tru

                         numeric value v
                      ---------------------                       (ST_IszroScc)
                      iszro (scc v) --> fls

                            t1 --> t1'
                       ----------------------                         (ST_Iszro)
                       iszro t1 --> iszro t1'
*)

(** ... and then formally: *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_TestTru : forall t1 t2,
      (test tru t1 t2) --> t1
  | ST_TestFls : forall t1 t2,
      (test fls t1 t2) --> t2
  | ST_Test : forall t1 t1' t2 t3,
      t1 --> t1' ->
      (test t1 t2 t3) --> (test t1' t2 t3)
  | ST_Scc : forall t1 t1',
      t1 --> t1' ->
      (scc t1) --> (scc t1')
  | ST_PrdZro :
      (prd zro) --> zro
  | ST_PrdScc : forall v,
      nvalue v ->
      (prd (scc v)) --> v
  | ST_Prd : forall t1 t1',
      t1 --> t1' ->
      (prd t1) --> (prd t1')
  | ST_IszroZro :
      (iszro zro) --> tru
  | ST_IszroScc : forall v,
       nvalue v ->
      (iszro (scc v)) --> fls
  | ST_Iszro : forall t1 t1',
      t1 --> t1' ->
      (iszro t1) --> (iszro t1')

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(** Notice that the [step] relation doesn't care about whether the
    expression being stepped makes global sense -- it just checks that
    the operation in the _next_ reduction step is being applied to the
    right kinds of operands.  For example, the term [scc tru] cannot
    take a step, but the almost as obviously nonsensical term

       scc (test tru then tru else tru)

    can take a step (once, before becoming stuck). *)

(* ================================================================= *)
(** ** Normal Forms and Values *)

(** The first interesting thing to notice about this [step] relation
    is that the strong progress theorem from the [Smallstep]
    chapter fails here.  That is, there are terms that are normal
    forms (they can't take a step) but not values (they are not
    included in our definition of possible "results of reduction").
    Such terms are said to be _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t : tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck : core.

(** **** Exercise: 2 stars, standard (some_term_is_stuck) *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  exists (scc tru).
  unfold stuck. split.
  + unfold step_normal_form. unfold not; intros.
    destruct H. inversion H. inversion H1.
  + unfold not; intros. inversion H.
    - inversion H0.
    - inversion H0. inversion H2.
Qed.    

(** [] *)

(** However, although values and normal forms are _not_ the same in
    this language, the set of values is a subset of the set of normal
    forms.  This is important because it shows we did not accidentally
    define things so that some value could still take a step. *)

(** **** Exercise: 3 stars, standard (value_is_nf) *)
Lemma value_is_nf : forall t,
  value t -> step_normal_form t.
Proof.
  (* FILL IN HERE *) Admitted.

(** (Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways.)

    [] *)


(* ================================================================= *)
(** ** Typing *)

(** The next critical observation is that, although this
    language has stuck terms, they are always nonsensical, mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

(** In informal notation, the typing relation is often written
    [ |- t \in T] and pronounced "[t] has type [T]."  The [|-] symbol
    is called a "turnstile."  Below, we're going to see richer typing
    relations where one or more additional "context" arguments are
    written to the left of the turnstile.  For the moment, the context
    is always empty.

    
                           ---------------                     (T_Tru)
                           |- tru \in Bool

                          ---------------                      (T_Fls)
                          |- fls \in Bool

             |- t1 \in Bool    |- t2 \in T    |- t3 \in T
             --------------------------------------------     (T_Test)
                    |- test t1 then t2 else t3 \in T

                             --------------                    (T_Zro)
                             |- zro \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Scc)
                          |- scc t1 \in Nat

                            |- t1 \in Nat
                          -----------------                    (T_Prd)
                          |- prd t1 \in Nat

                            |- t1 \in Nat
                        --------------------                 (T_IsZro)
                        |- iszro t1 \in Bool
*)

Reserved Notation "'|-' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_Tru :
       |- tru \in Bool
  | T_Fls :
       |- fls \in Bool
  | T_Test : forall t1 t2 t3 T,
       |- t1 \in Bool ->
       |- t2 \in T ->
       |- t3 \in T ->
       |- test t1 t2 t3 \in T
  | T_Zro :
       |- zro \in Nat
  | T_Scc : forall t1,
       |- t1 \in Nat ->
       |- scc t1 \in Nat
  | T_Prd : forall t1,
       |- t1 \in Nat ->
       |- prd t1 \in Nat
  | T_Iszro : forall t1,
       |- t1 \in Nat ->
       |- iszro t1 \in Bool

where "'|-' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |- test fls zro (scc zro) \in Nat.
Proof.
  apply T_Test.
  + apply T_Fls.
  + apply T_Zro.
  + apply T_Scc. apply T_Zro.   
Qed.

(*          
        -------------- (T_Fls)
        |- fls \in Bool     
        
        --------------- (T_Zro)
        |- zro \in Nat    
        
          --------------- (T_Zro)
            |- zro \in Nat
        ----------------------- (T_Scc)
        |- scc zro \in Nat
      ------------------------------------------------------- (T_Test)
      |- test fls zro (scc zro) \in Nat
*)


(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not consider
    what happens when the term is reduced -- in particular, it does
    not calculate the type of its normal form. *)

Example has_type_not :
  ~ ( |- test fls zro tru \in Bool ).
Proof.
  intros Contra. solve_by_inverts 2.  Qed.


(* ----------------------------------------------------------------- *)
(** *** Canonical forms *)

(** The following two lemmas capture the fundamental property that the
    definitions of boolean and numeric values agree with the typing
    relation. *)

Lemma bool_canonical : forall t,
  |- t \in Bool -> value t -> bvalue t.
Proof.
  intros t HT [Hb | Hn].
  - assumption.
  - destruct Hn as [ | Hs].
    + inversion HT.
    + inversion HT.
Qed.

Lemma nat_canonical : forall t,
  |- t \in Nat -> value t -> nvalue t.
Proof.
  intros t HT [Hb | Hn].
  - inversion Hb; subst; inversion HT.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are not stuck -- or conversely, if a
    term is well typed, then either it is a value or it can take at
    least one step.  We call this _progress_. *)

(** **** Exercise: 3 stars, standard (finish_progress) *)
Theorem progress : forall t T,
  |- t \in T ->
  value t \/ exists t', t --> t'.

(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the parts we've given of the informal proof in the
    following exercise before starting -- this will save you a lot of
    time.) *)
Proof.
  intros t T HT.
  induction HT; auto.
  (* The cases that were obviously values, like T_Tru and
     T_Fls, are eliminated immediately by auto *)
  - (* T_Test *)
    right. destruct IHHT1.
    + (* t1 is a value *)
    apply (bool_canonical t1 HT1) in H.
    destruct H.
      * exists t2. auto.
      * exists t3. auto.
    + (* t1 can take a step *)
      destruct H as [t1' H1].
      exists (test t1' t2 t3). auto.
  - (* T_Scc *)
    destruct IHHT. apply (nat_canonical t1 HT) in H.
    destruct H.
    + auto. 
    + auto 6.
    + destruct H. right. exists (scc x). auto.
  - (* Case T_Prd *)
    destruct IHHT. apply (nat_canonical t1 HT) in H.
    destruct H.
    + right. exists zro; auto.
    + right. exists t. auto.
    + right. destruct H. exists (prd x). auto.
  - (* Case T_IsZro *)
    destruct IHHT. apply (nat_canonical t1 HT) in H.
    destruct H.
    + right. exists tru. auto.
    + right. exists fls. auto.
    + right. destruct H. exists (iszro x). auto.
Qed.

(*

  (* FILL IN HERE *) Admitted.
(** [] *)


*)      


(* ================================================================= *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is a well-typed term (of the same type). *)

(** **** Exercise: 2 stars, standard (finish_preservation) *)
Theorem preservation : forall t t' T,
  |- t \in T ->
  t --> t' ->
  |- t' \in T.
Proof.
  intros t t' T HT HE.
  generalize dependent t'.
  induction HT;
         (* every case needs to introduce a couple of things *)
         intros t' HE;
         (* and we can deal with several impossible
            cases all at once *)
         try solve_by_invert.
    - (* T_Test *) inversion HE; subst.
      + (* ST_TESTTru *) assumption.
      + (* ST_TestFls *) assumption.
      + (* ST_Test *) apply T_Test; try assumption.
        apply IHHT1; assumption.
    - (* T_Scc *) inversion HE; subst. apply T_Scc. 
      apply IHHT; try assumption.
    - (* T_Prd *) inversion HE; subst; auto.
      inversion HT; subst; auto.
    - (* T_isZro *) inversion HE; subst; auto.
Qed.   

(*
    (* FILL IN HERE *) Admitted.
(** [] *)
*)
(* ================================================================= *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we see that a
    well-typed term can never reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Corollary soundness : forall t t' T,
  |- t \in T ->
  t -->* t' ->
  ~(stuck t').
Proof.
  intros t t' T HT P. induction P; intros [R S].
  - apply progress in HT. destruct HT; auto.
  - apply IHP.
    + apply preservation with (t := x); auto.
    + unfold stuck. split; auto.
Qed.


