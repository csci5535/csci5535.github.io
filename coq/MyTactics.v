Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export Poly.

(* ================================================================= *)
(** ************************ TACTICS ************************ *)
(* ================================================================= *)

(* ################################################################# *)
(** * The [apply] Tactic *)

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. Qed. 

(* Conditional hypothesis *)
Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
  intros n m o p H1 H2.
  apply H2. apply H1.
Qed.

(* Quantified hypothesis *)
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof. intros n m H1 H2. apply H2. apply H1. Qed. 

(* ################################################################# *)
(** * The [apply with] Tactic *)

Example trans_eq_example : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
 intros a b c d e f eq1 eq2.
 rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might like to pull it out as a
   lemma that records, once and for all, the fact that equality is
   transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
 n = m -> m = o -> n = o.
Proof.
 intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
 reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to prove the above
   example.  However, to do this we need a slight refinement of the
   [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
    [a;b] = [c;d] ->
    [c;d] = [e;f] ->
    [a;b] = [e;f].
Proof.
 intros a b c d e f eq1 eq2.
 apply trans_eq with (m:=[c;d]).
 apply eq1. apply eq2.
 (* apply (trans_eq (list nat) [a;b] [c;d] [e;f] eq1 eq2).*)
 Qed.

(* ################################################################# *)
(** * The [injection] and [discriminate] Tactics *)

(** Recall the definition of natural numbers:

     Inductive nat : Type :=
       | O
       | S (n : nat).

    It is obvious from this definition that every number has one of
    two forms: either it is the constructor [O] or it is built by
    applying the constructor [S] to another number.  But there is more
    here than meets the eye: implicit in the definition are two
    additional facts:

    - The constructor [S] is _injective_ (or _one-to-one_).  That is,
      if [S n = S m], it must be that [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)


(* Coq provides [injection] tactic that lets us take advantage of injectivity 
   of constructors *)

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Heq. apply Heq.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as Heq1 Heq2.
  rewrite Heq1. rewrite Heq2. reflexivity.
Qed.

(** The principle of disjointness says that two terms beginning
    with different constructors (like [O] and [S], or [true] and [false])
    can never be equal.  This means that, any time we find ourselves
    in a context where we've _assumed_ that two such terms are equal,
    we are justified in concluding anything we want, since the
    assumption is nonsensical. *)

(** The [discriminate] tactic embodies this principle: It is used on a
    hypothesis involving an equality between different
    constructors (e.g., [false = true]), and it solves the current
    goal immediately.  Some examples: *)

Theorem discriminate_ex2 : forall (n : nat),
    S n = O ->
    2 + 2 = 5.
Proof.
  intros n absurdity.
  discriminate absurdity.
Qed.

Theorem eqb_0_l : forall n,
    0 =? n = true -> n = 0.
 Proof.
   intros n.
   destruct n as [| n'] eqn:E.
   - (* n = 0 *)
     intros H. reflexivity.
 
   - (* n = S n' *)
     simpl.
     intros H. discriminate H.
 Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
 x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.

(* ################################################################# *)
(** * Using Tactics on Hypotheses *)


(* simpl *)
Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b  ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H.
Qed.

(* apply and symmetry *)
Theorem modus_ponens : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q H1 H2. symmetry in H2. 
  apply H1 in H2. symmetry. apply H2.
Qed.

(* ################################################################# *)
(** * Varying the Induction Hypothesis *)

Print double.

Compute (double 0).

Compute (double 1).

Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m. destruct m as [| m'].
    + simpl. reflexivity.
    + intros H. discriminate H.
  - intros m H. destruct m as [| m'].
    + discriminate.
    + apply f_equal. simpl in H. injection H. apply IHn'.
Qed.


(* ################################################################# *)
(** * Review *)

(** We've now seen many of Coq's most fundamental tactics.  We'll
    introduce a few more in the coming chapters, and later on we'll
    see some more powerful _automation_ tactics that make Coq help us
    with low-level details.  But basically we've got what we need to
    get work done.

    Here are the ones we've seen:

      - [intros]: move hypotheses/variables from goal to context

      - [reflexivity]: finish the proof (when the goal looks like [e =
        e])

      - [apply]: prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: apply a hypothesis, lemma, or constructor to
        a hypothesis in the context (forward reasoning)

      - [apply... with...]: explicitly specify values for variables
        that cannot be determined by pattern matching

      - [simpl]: simplify computations in the goal

      - [simpl in H]: ... or a hypothesis

      - [rewrite]: use an equality hypothesis (or lemma) to rewrite
        the goal

      - [rewrite ... in H]: ... or a hypothesis

      - [symmetry]: changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]: changes a hypothesis of the form [t=u] into
        [u=t]

      - [transitivity y]: prove a goal [x=z] by proving two new subgoals,
        [x=y] and [y=z]

      - [unfold]: replace a defined constant by its right-hand side in
        the goal

      - [unfold... in H]: ... or a hypothesis

      - [destruct... as...]: case analysis on values of inductively
        defined types

      - [destruct... eqn:...]: specify the name of an equation to be
        added to the context, recording the result of the case
        analysis

      - [induction... as...]: induction on values of inductively
        defined types

      - [injection... as...]: reason by injectivity on equalities
        between values of inductively defined types

      - [discriminate]: reason by disjointness of constructors on
        equalities between values of inductively defined types

      - [assert (H: e)] (or [assert (e) as H]): introduce a "local
      lemma" [e] and call it [H]

      - [generalize dependent x]: move the variable [x] (and anything
        else that depends on it) from the context back to an explicit
        hypothesis in the goal formula

      - [f_equal]: change a goal of the form [f x = f y] into [x = y] *)

(* ################################################################# *)
