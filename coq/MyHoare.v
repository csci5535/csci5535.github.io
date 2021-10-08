(** * Hoare: Hoare Logic, Part I *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From LF Require Export Imp.

(** In the final chaper of _Logical Foundations_ (_Software
    Foundations_, volume 1), we began applying the mathematical tools
    developed in the first part of the course to studying the theory
    of a small programming language, Imp.

    - Imp: _abstract sytax trees_ and _operational semantics_.

      The language we defined, though small, captures some of the key
      features of full-blown languages like C, C++, and Java,
      including the fundamental notion of mutable state and some
      common control structures.

    -_metatheoretic properties_ :

        - determinism of evaluation

        - equivalence of some different ways of writing down the
          definitions (e.g., functional and relational definitions of
          arithmetic expression evaluation)

        - guaranteed termination of certain classes of programs

        - correctness (in the sense of preserving meaning) of a some
          useful program transformations *)

(** What we have: a set
    of tools for defining and discussing programming languages and
    language features that are mathematically precise, flexible, and
    easy to work with, applied to a set of key properties.  
*)

(** Next - Program Verification: Our goal is to carry out 
    some  simple examples of _program verification_ -- i.e., 
    to use the precise definition of Imp to prove formally 
    that particular programs satisfy particular specifications 
    of their behavior.  We'll develop a reasoning system called 
    _Floyd-Hoare Logic_ -- often shortened to just
    _Hoare Logic_ -- in which each of the syntactic constructs
    of Imp is equipped with a generic "proof rule" that can be 
    used to reason compositionally about the correctness of programs 
    involving this construct.

    Hoare Logic originated in the 1960s, and it continues to be the
    subject of intensive research right up to the present day.  It
    lies at the core of a multitude of tools that are being used in
    academia and industry to specify and verify real software systems.

    Hoare Logic combines two beautiful ideas: 
      1. A natural way of writing down _specifications_ of 
         programs, and 
      2. A _compositional proof technique_ for proving that 
         programs are correct with respect to such specifications. 
      
      
      "compositional" => structure of proofs directly mirrors the 
      structure of the programs that they are about. *)

(* ################################################################# *)
(** * Assertions *)

(** An _assertion_ is a claim about the current state of memory. We will
    use assertions to write program specifications. *)

Definition Assertion := state -> Prop.

(** For example,

    - [fun st => st X = 3] holds if the value of [X] according to [st] is [3],

    - [fun st => True] always holds, and

    - [fun st => False] never holds. *)

(** **** Exercise: 1 star, standard, optional (assertions)

    Paraphrase the following assertions in English (or your favorite
    natural language). *)

Module ExAssertions.
Definition assn1 : Assertion := fun st => st X <= st Y.
Definition assn2 : Assertion :=
  fun st => st X = 3 \/ st X <= st Y.
Definition assn3 : Assertion :=
  fun st => st Z * st Z <= st X /\
            ~ (((S (st Z)) * (S (st Z))) <= st X).
Definition assn4 : Assertion :=
  fun st => st Z = max (st X) (st Y).
(* FILL IN HERE *)
End ExAssertions.
(** [] *)

(** Notation: Instead of writing

      fun st => st X = m

    we'll write just

      X = m
*)

(** This example also illustrates a convention that we'll use
    throughout the Hoare Logic chapters: in informal assertions,
    capital letters like [X], [Y], and [Z] are Imp variables, while
    lowercase letters like [x], [y], [m], and [n] are ordinary Coq
    variables (of type [nat]).  This is why, when translating from
    informal to formal, we replace [X] with [st X] but leave [m]
    alone. *)

(** Given two assertions [P] and [Q], we say that [P] _implies_ [Q],
    written [P ->> Q], if, whenever [P] holds in some state [st], [Q]
    also holds. *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

(** (The [hoare_spec_scope] annotation here tells Coq that this
    notation is not global but is intended to be used in particular
    contexts.  The [Open Scope] tells Coq that this file is one such
    context.) *)

(** We'll also want the "iff" variant of implication between
    assertions: *)

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

(* ================================================================= *)
(** ** Notations for Assertions *)

(** There is no need to understand the details. *)

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

(** One small limitation of this approach is that we don't have
    an automatic way to coerce function applications that appear
    within an assertion to make appropriate use of the state.
    Instead, we use an explicit [ap] operator to lift the function. *)

Definition ap {X} (f : nat -> X) (x : Aexp) :=
  fun st => f (x st).

Definition ap2 {X} (f : nat -> nat -> X) (x : Aexp) (y : Aexp) (st : state) :=
  f (x st) (y st).

Module ExPrettyAssertions.
Definition ex1 : Assertion := X = 3.
Definition ex2 : Assertion := True.
Definition ex3 : Assertion := False.

Definition assn1 : Assertion := X <= Y.
Definition assn2 : Assertion := X = 3 \/ X <= Y.
Definition assn3 : Assertion :=
  Z * Z <= X  /\  ~ (((ap S Z) * (ap S Z)) <= X).
Definition assn4 : Assertion :=
  Z = ap2 max X Y.
End ExPrettyAssertions.

(* ################################################################# *)
(** * Hoare Triples, Informally *)

(** A _Hoare triple_ is a claim about the state before and after executing
    a command.  A standard notation is

      {P} c {Q}

    meaning:

      - If command [c] begins execution in a state satisfying assertion [P],
      - and if [c] eventually terminates in some final state,
      - then that final state will satisfy the assertion [Q].

    Assertion [P] is called the _precondition_ of the triple, and [Q] is
    the _postcondition_.

    Because single braces are already used for other things in Coq, we'll write
    Hoare triples with double braces:

       {{P}} c {{Q}}
*)
(** For example,

    - [{{X = 0}} X := X + 1 {{X = 1}}] is a valid Hoare triple,
      stating that command [X := X + 1] would transform a state in
      which [X = 0] to a state in which [X = 1].

    - [forall m, {{X = m}} X := X + 1 {{X = m + 1}}], is a
      _proposition_ stating that the Hoare triple [{{X = m}} X := X +
      m {{X = m * 2}}]) is valid for any choice of [m].  Note that [m]
      in the two assertions and the command in the middle is a
      reference to the Coq variable [m], which is bound outside the
      Hoare triple, not to an Imp variable. *)

(** **** Exercise: 1 star, standard, optional (triples)

    Paraphrase the following in English.

     1) {{True}} c {{X = 5}}

     2) forall m, {{X = m}} c {{X = m + 5)}}

     3) {{X <= Y}} c {{Y <= X}}

     4) {{True}} c {{False}}

     5) forall m,
          {{X = m}}
          c
          {{Y = real_fact m}}

     6) forall m,
          {{X = m}}
          c
          {{(Z * Z) <= m /\ ~ (((S Z) * (S Z)) <= m)}}
*)
(* FILL IN HERE

    [] *)

(** **** Exercise: 1 star, standard, optional (valid_triples)

    Which of the following Hoare triples are _valid_ -- i.e., the
    claimed relation between [P], [c], and [Q] is true?

   1) {{True}} X := 5 {{X = 5}}

   2) {{X = 2}} X := X + 1 {{X = 3}}

   3) {{True}} X := 5; Y := 0 {{X = 5}}

   4) {{X = 2 /\ X = 3}} X := 5 {{X = 0}}

   5) {{True}} skip {{False}}

   6) {{False}} skip {{True}}

   7) {{True}} while true do skip end {{False}}

   8) {{X = 0}}
        while X = 0 do X := X + 1 end
      {{X = 1}}

   9) {{X = 1}}
        while ~(X = 0) do X := X + 1 end
      {{X = 100}}
*)
(* FILL IN HERE

    [] *)

(* ################################################################# *)
(** * Hoare Triples, Formally *)

(** We can formalize Hoare triples and their notation in Coq as follows: *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
  st =[c]=>st' ->
  P st ->
  Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.
Check ({{True}} X := 0 {{True}}).

(** **** Exercise: 1 star, standard (hoare_post_true) *)

(** Prove that if [Q] holds in every state, then any triple with [Q]
    as its postcondition is valid. *)

Theorem hoare_post_true : forall (P Q : Assertion) c,
  (forall st, Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros.
  unfold hoare_triple.
  intros.
  apply H.
Qed.

(** **** Exercise: 1 star, standard (hoare_pre_false) *)

(** Prove that if [P] holds in no state, then any triple with [P] as
    its precondition is valid. *)

Theorem hoare_pre_false : forall (P Q : Assertion) c,
  (forall st, ~ (P st)) ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple.
  intros.
  exfalso.
  repeat (unfold not in H; apply H with (st:=st));
  assumption.
Qed.

(* ################################################################# *)
(** * Proof Rules *)

(** One rule to reason about each syntactic form in Imp.  We
    will then be able to prove programs correct using these proof
    rules, without ever unfolding the definition of [hoare_triple]. *)

(* ================================================================= *)
(** ** Assignment *)

(** The rule for assignment is the most fundamental of the Hoare
    logic proof rules.  Here's how it works.

    Consider this incomplete Hoare triple:

       {{ Y=1}}  X := Y  {{ X = 1 }}
 *)




(** That same idea works in more complicated cases.  For
    example:

       {{ X+Y = 1 }}  X := X + Y  {{ X = 1 }}






    Why does this technique work?  *)


(** In general, the postcondition could be some arbitrary assertion
    [Q], and the right-hand side of the assignment could be some
    arbitrary arithmetic expression [a]:

       {{ Q[x |-> a] }}  X := a  {{ Q }}
      

    That yields the Hoare logic rule for assignment:

      {{ Q [X |-> a] }}  X := a  {{ Q }}

    One way of reading that rule is: If you want statement [X := a]
    to terminate in a state that satisfies assertion [Q], then it
    suffices to start in a state that also satisfies [Q], except
    where [a] is substituted for every occurrence of [X].

    To many people, this rule seems "backwards" at first, because
    it proceeds from the postcondition to the precondition.  Actually
    it makes good sense to go in this direction: the postcondition is
    often what is more important, because it characterizes what we
    can assume afer running the code.

    Nonetheless, it's also possible to formulate a "forward" assignment
    rule.  We'll do that later in some exercises. *)

(** Fill in the following:

      {{ X <= 4}}     
      X := X + 1
      {{ X <= 5 }}

      {{ true   }}  
      X := 3
      {{ X = 3 }}

      {{ true }}
      X := 3
      {{ 0 <= X /\ X <= 5 }}
*)

(** To formalize the rule, we must first formalize the idea of
    "substituting an expression for an Imp variable in an assertion",
    which we refer to as assertion substitution, or [assn_sub].  That
    is, given a proposition [P], a variable [X], and an arithmetic
    expression [a], we want to derive another proposition [P'] that is
    just the same as [P] except that [P'] should mention [a] wherever
    [P] mentions [X]. *)

(** Since [P] is an arbitrary Coq assertion, we can't directly "edit"
    its text.  However, we can achieve the same effect by evaluating
    [P] in an updated state: *)

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).

(** That is, [P [X |-> a]] stands for an assertion -- let's call it [P'] --
    that is just like [P] except that, wherever [P] looks up the
    variable [X] in the current state, [P'] instead uses the value
    of the expression [a]. *)



(** Substitution Example: suppose [P'] is [(X <= 5) [X |->
    X + 1]].  Formally, [P'] is the Coq expression

    fun st =>
      (fun st' => st' X <= 5)
      (X !-> aeval st (X + 1) ; st),

    which simplifies to

    fun st =>
      (X !-> aeval st (X + 1) ; st) X <= 5

    and further simplifies to

    fun st =>
      (aeval st (X + 1)) <= 5.

    That is, [P'] is the assertion that [X + 1] is at most [5].
*)

(** Now, using the concept of substitution, we can give the precise
    proof rule for assignment:

      ------------------------------ (hoare_asgn)
      {{Q [X |-> a]}} X := a {{Q}}
*)

(** We can prove formally that this rule is indeed valid. *)

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple, assn_sub.
  intros.
  inversion H. subst.
  assumption.
Qed.

(** Here's a first formal proof using this rule. *)

Example assn_sub_example :
  {{(X < 5) [X |-> X + 1]}}
  X := X + 1
  {{X < 5}}.
Proof.
apply hoare_asgn.
Qed.


(** Complete these Hoare triples by providing an appropriate
    precondition using [exists], then prove then with [apply
    hoare_asgn]. If you find that tactic doesn't suffice, double check
    that you have completed the triple properly. *)
(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples1) *)
Example hoare_asgn_examples1 :
  exists P,
    {{ P }}
      X := 2 * X
    {{ X <= 10 }}.
Proof.
  exists ((X <= 10)[X |-> 2*X]).
  apply hoare_asgn.
Qed.

(** **** Exercise: 2 stars, standard, optional (hoare_asgn_examples2) *)
Example hoare_asgn_examples2 :
  exists P,
    {{ P }}
      X := 3
    {{ 0 <=  X /\ X <= 5 }}.
Proof. 
  exists ((0 <=  X /\ X <= 5) [X |-> 3]).
  apply hoare_asgn.
Qed.


(* ================================================================= *)
(** ** Consequence *)

(** Sometimes the preconditions and postconditions we get from the
    Hoare rules won't quite be the ones we want in the particular
    situation at hand -- they may be logically equivalent but have a
    different syntactic form that fails to unify with the goal we are
    trying to prove, or they actually may be logically weaker (for
    preconditions) or stronger (for postconditions) than what we need. *)

(** For instance, while

      {{(X = 3) [X |-> 3]}} X := 3 {{X = 3}},

    follows directly from the assignment rule,

      {{True}} X := 3 {{X = 3}}

    does not.  This triple is valid, but it is not an instance of
    [hoare_asgn] because [True] and [(X = 3) [X |-> 3]] are not
    syntactically equal assertions.  However, they are logically
    _equivalent_, so if one triple is valid, then the other must
    certainly be as well.  We can capture this observation with the
    following rule:

                {{P'}} c {{Q}}
                  P <<->> P'
         -----------------------------   (hoare_consequence_pre_equiv)
                {{P}} c {{Q}}
*)

(** Taking this line of thought a bit further, we can see that
    strengthening the precondition or weakening the postcondition of a
    valid triple always produces another valid triple. This
    observation is captured by two _Rules of Consequence_.

                {{P'}} c {{Q}}
                   P ->> P'
         -----------------------------   (hoare_consequence_pre)
                {{P}} c {{Q}}

                {{P}} c {{Q'}}
                  Q' ->> Q
         -----------------------------    (hoare_consequence_post)
                {{P}} c {{Q}}
*)

(** Here are the formal versions: *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold "->>", hoare_triple. intros.
  apply H with (st:=st).
  + assumption.
  + apply H0. assumption.
Qed.  


Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.

(** For example, we can use the first consequence rule like this:

      {{ True }} ->>
      {{ (X = 1) [X |-> 1] }}
    X := 1
      {{ X = 1 }}

    Or, formally... *)

Example hoare_asgn_example1 :
  {{True}} X := 1 {{X = 1}}.
Proof.
  apply hoare_consequence_pre with (P' := ((X = 1)[X |-> 1]) ).
  + apply hoare_asgn.
  + unfold "->>", assn_sub. intros. simpl. unfold t_update. simpl. reflexivity. 
Qed.
(** We can also use it to prove the example mentioned earlier.

      {{ X < 4 }} ->>
      {{ (X < 5)[X |-> X + 1] }}
    X := X + 1
      {{ X < 5 }}

   Or, formally ... *)

Example assn_sub_example2 :
  {{X < 4}}
  X := X + 1
  {{X < 5}}.
Proof.
  apply hoare_consequence_pre with (P' := ((X < 5)[X |-> X+1])).
  + apply hoare_asgn.
  + unfold "->>", assn_sub, t_update. simpl. intros. lia.
Qed.  

(** Finally, here is a combined rule of consequence that allows us to
    vary both the precondition and the postcondition.

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}
*)

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.

(* ================================================================= *)
(** ** Automation *)

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.


Ltac assn_auto :=
  try auto;  (* as in example 1, above *)
  try (unfold "->>", assn_sub, t_update;
       intros; simpl in *; lia). (* as in example 2 *)

Example assn_sub_example2'' :
  {{X < 4}}
  X := X + 1
  {{X < 5}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

Example hoare_asgn_example1''':
  {{True}} X := 1 {{X = 1}}.
Proof.
  eapply hoare_consequence_pre.
  - apply hoare_asgn.
  - assn_auto.
Qed.

(* ================================================================= *)
(** ** Skip *)

(** Since [skip] doesn't change the state, it preserves any
    assertion [P]:

      --------------------  (hoare_skip)
      {{ P }} skip {{ P }}
*)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.

(* ================================================================= *)
(** ** Sequencing *)

(*
          {{P}} c1 {{R}}
          {{R}} c2 {{Q}}
        ---------------------
          {{ P}} c1;c2 {{ Q }}
*)


(** If command [c1] takes any state where [P] holds to a state where
    [Q] holds, and if [c2] takes any state where [Q] holds to one
    where [R] holds, then doing [c1] followed by [c2] will take any
    state where [P] holds to one where [R] holds:

        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ----------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.

(** Note that, in the formal rule [hoare_seq], the premises are
    given in backwards order ([c2] before [c1]).  This matches the
    natural flow of information in many of the situations where we'll
    use the rule, since the natural way to construct a Hoare-logic
    proof is to begin at the end of the program (with the final
    postcondition) and push postconditions backwards through commands
    until we reach the beginning. *)

(** Here's an example of a program involving sequencing.  Note the use
    of [hoare_seq] in conjunction with [hoare_consequence_pre] and the
    [eapply] tactic. *)

Example hoare_asgn_example3 : forall (a:aexp) (n:nat),
    {{a = n}}
  X := a;
  skip
    {{X = n}}.
Proof.
  intros.
  eapply hoare_seq.
  + apply hoare_skip.
  + eapply hoare_consequence_pre.
    - apply hoare_asgn.
    - assn_auto.
Qed.   

(** Informally, a nice way of displaying a proof using the sequencing
    rule is as a "decorated program" where the intermediate assertion
    [Q] is written between [c1] and [c2]:

      {{ a = n }}
    X := a;
      {{ X = n }}    <--- decoration for Q
    skip
      {{ X = n }}
*)


(* ================================================================= *)
(** ** Conditionals *)

(** What sort of rule do we want for reasoning about conditional
    commands?

    Certainly, if the same assertion [Q] holds after executing
    either of the branches, then it holds after the whole conditional.
    So we might be tempted to write:

              {{P}} c1 {{Q}}
              {{P}} c2 {{Q}}
      ---------------------------------
      {{P}} if b then c1 else c2 {{Q}}
*)

(** However, this is rather weak. For example, using this rule,
   we cannot show

     {{ True }}
     if X = 0
       then Y := 2
       else Y := X + 1
     end
     {{ X <= Y }}

   since the rule tells us nothing about the state in which the
   assignments take place in the "then" and "else" branches. *)

(** Fortunately, we can say something more precise.  In the
    "then" branch, we know that the boolean expression [b] evaluates to
    [true], and in the "else" branch, we know it evaluates to [false].
    Making this information available in the premises of the rule gives
    us more information to work with when reasoning about the behavior
    of [c1] and [c2] (i.e., the reasons why they establish the
    postcondition [Q]).

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}
*)

(** To interpret this rule formally, we need to do a little work.
    Strictly speaking, the assertion we've written, [P /\ b], is the
    conjunction of an assertion and a boolean expression -- i.e., it
    doesn't typecheck.  To fix this, we need a way of formally
    "lifting" any bexp [b] to an assertion.  We'll write [bassn b] for
    the assertion "the boolean expression [b] evaluates to [true] (in
    the given state)." *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.

Arguments bassn /.

(** A useful fact about [bassn]: *)

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

(** We mentioned the [congruence] tactic in passing in [Auto] when
    building the [find_rwd] tactic.  Like [find_rwd], [congruence] is able to
    automatically find that both [beval st b = false] and [beval st b = true]
    are being assumed, notice the contradiction, and [discriminate] to complete
    the proof. *)

(** Now we can formalize the Hoare proof rule for conditionals
    and prove it correct. *)

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
(** That is (unwrapping the notations):

      Theorem hoare_if : forall P Q b c1 c2,
        {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
        {{fun st => P st /\ ~ (bassn b st)}} c2 {{Q}} ->
        {{P}} if b then c1 else c2 end {{Q}}.
*)
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

(* ----------------------------------------------------------------- *)
(** *** Example *)

(** Here is a formal proof that the program we used to motivate the
    rule satisfies the specification we gave. *)

Example if_example :
    {{True}}
  if (X = 0)
    then Y := 2
    else Y := X + 1
  end
    {{X <= Y}}.
Proof.
  apply hoare_if.
  + eapply hoare_consequence_pre.
    - apply hoare_asgn.
    - unfold "->>", assn_sub, t_update.
      simpl. intros. destruct H. apply eqb_eq in H0. rewrite H0. lia.
  + eapply hoare_consequence_pre.
    - apply hoare_asgn.
    - unfold "->>", assn_sub, t_update.
      intros. simpl in *. lia.
Qed.



(* ================================================================= *)
(** ** While Loops *)

(*
                {{P /\ b}} c {{Q}}
                P /\ ~b ->> Q
          -----------------------------
          {{ P }} While b do c end {{Q}}

*)


(**  As a first attempt at a [while] rule, we could try:

             {{P}} c {{P}}
      ---------------------------
      {{P} while b do c end {{P}}

    That rule is valid: if [P] is an invariant of [c], as the premise
    requires, then no matter how many times the loop body executes,
    [P] is going to be true when the loop finally finishes.

    But the rule also omits two crucial pieces of information.  First,
    the loop terminates when [b] becomes false.  So we can strengthen
    the postcondition in the conclusion:

              {{P}} c {{P}}
      ---------------------------------
      {{P} while b do c end {{P /\ ~b}}

    Second, the loop body will be executed only if [b] is true.  So we
    can also strengthen the precondition in the premise:

            {{P /\ b}} c {{P}}
      --------------------------------- (hoare_while)
      {{P} while b do c end {{P /\ ~b}}
*)

(** That is the Hoare [while] rule.  Note how it combines
    aspects of [skip] and conditionals:

    - If the loop body executes zero times, the rule is like [skip] in
      that the precondition survives to become (part of) the
      postcondition.

    - Like a conditional, we can assume guard [b] holds on entry to
      the subcommand.
*)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.

(** We call that [P] a _loop invariant_ of [while b do c end] if

      {{P /\ b}} c {{P}}

    holds. This means that [P] remains true whenever the loop executes.
    If [P] contradicts [b], this holds trivially since the precondition
    is false. For instance, [X = 0] is a loop invariant of

      while X = 2 do X := 1 end

    since we will never enter the loop. *)

Example while_example :
    {{X <= 3}}
  while (X <= 2) do
    X := X + 1
  end
    {{X = 3}}.
Proof.
  eapply hoare_consequence_post.
  - apply hoare_while.
    eapply hoare_consequence_pre.
    + apply hoare_asgn.
    + unfold "->>", assn_sub, t_update.
      simpl in *. intros. destruct H.
      assert (st X <= 2).
      {
       apply leb_le. assumption. 
      }
      lia. 
  - unfold "->>", assn_sub, t_update.
    simpl in *. intros. destruct H.
    assert (not (st X <= 2)). 
    {
     unfold not; intros. eapply leb_le in H1. contradiction.
    }
    lia.
Qed.

(** If the loop never terminates, any postcondition will work. *)

Theorem always_loop_hoare : forall Q,
  {{True}} while true do skip end {{Q}}.
Proof.
  intros Q.
  eapply hoare_consequence_post.
  - apply hoare_while. apply hoare_post_true. auto.
  - simpl. intros st [Hinv Hguard]. congruence.
Qed.

(** Of course, this result is not surprising if we remember that
    the definition of [hoare_triple] asserts that the postcondition
    must hold _only_ when the command terminates.  If the command
    doesn't terminate, we can prove anything we like about the
    post-condition.

    Hoare rules that specify what happens _if_ commands terminate,
    without proving that they do, are said to describe a logic of
    _partial_ correctness.  It is also possible to give Hoare rules
    for _total_ correctness, which additionally specifies that
    commands must terminate. Total correctness is out of the scope of
    this textbook. *)



(* ################################################################# *)
(** * Summary *)

(** So far, we've introduced Hoare Logic as a tool for reasoning about
    Imp programs.

    The rules of Hoare Logic are:

             --------------------------- (hoare_asgn)
             {{Q [X |-> a]}} X:=a {{Q}}

             --------------------  (hoare_skip)
             {{ P }} skip {{ P }}

               {{ P }} c1 {{ Q }}
               {{ Q }} c2 {{ R }}
              ----------------------  (hoare_seq)
              {{ P }} c1;c2 {{ R }}

              {{P /\   b}} c1 {{Q}}
              {{P /\ ~ b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} if b then c1 else c2 end {{Q}}

               {{P /\ b}} c {{P}}
        -----------------------------------  (hoare_while)
        {{P}} while b do c end {{P /\ ~ b}}

                {{P'}} c {{Q'}}
                   P ->> P'
                   Q' ->> Q
         -----------------------------   (hoare_consequence)
                {{P}} c {{Q}}

    In the next chapter, we'll see how these rules are used to prove
    that more interesting programs satisfy interesting specifications of
    their behavior. *)
