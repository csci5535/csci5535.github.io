(* Functional Programming in Coq *)

(* Days of the week example *)
Inductive day : Type := 
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* next_weekday function *)
Definition next_weekday (d:day) : day := 
  match d with
   | monday => tuesday
   | tuesday => wednesday
   | wednesday => thursday
   | thursday => friday
   | _  => monday
  end.


(* Compute lets you perform computation and see the result *)

Compute (next_weekday monday).
(* Example *)


Example my_next_weekday_assertion: (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(* bool type *)
Inductive bool : Type := 
  | true
  | false.

(* negb definition *)
Definition negb (b:bool) : bool := 
    match b with 
    | true => false
    | false => true
    end.

(* orb definition *)
Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with
  | true => true
  | false => b2
  end.

(* Write an example to test orb *)
Example test_orb1:  (orb true  false) = true.
Proof. simpl. reflexivity. Qed. 

(* andb definition *)
Definition andb (b1:bool) (b2:bool) : bool := 
  match b1 with
  | false => false
  | true => b2
  end.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).  

Compute (true && false).

(* Conditional expressions *)
Definition orb' (b1:bool) (b2:bool) : bool := 
  if b1 then true else false.
(* ================================================================= *)
(** ** Types *)

(* Check *)

Check true.

Check (next_weekday tuesday).

Check negb.

Check bool.

(* ================================================================= *)
(** ** New Types from Old *)
Inductive rgb : Type :=
  | red
  | green
  | blue.

(* Color type *)
Inductive color : Type :=
  | black
  | white
  | primary (p:rgb).

(** The definitions of [rgb] and [color] say
    which constructor expressions belong to the sets [rgb] and
    [color]:

    - [red], [green], and [blue] belong to the set [rgb];
    - [black] and [white] belong to the set [color];
    - if [p] is a constructor expression belonging to the set [rgb],
      then [primary p] (pronounced "the constructor [primary] applied
      to the argument [p]") is a constructor expression belonging to
      the set [color]; and
    - constructor expressions formed in these ways are the _only_ ones
      belonging to the sets [rgb] and [color]. *)

(* isRed function *)

(* ================================================================= *)
(** ** Modules *)
Module Playground.
  Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check Playground.b : rgb.
Check b : bool.


(* ================================================================= *)
(** ** Numbers *)

Module NatPlayground.

(* Define nat *)
Inductive nat : Type := 
  | O
  | S (n:nat).

Check S (S O).

Check S.

(** The definition of [nat] says how expressions in the set [nat] can be built:

    - the constructor expression [O] belongs to the set [nat];
    - if [n] is a constructor expression belonging to the set [nat],
      then [S n] is also a constructor expression belonging to the set
      [nat]; and
    - constructor expressions formed in these two ways are the only
      ones belonging to the set [nat]. *)

(* Define pred function *)
Fixpoint pred (n: nat) : nat := 
  match n with
  | O => O
  | S p => p
  end.

End NatPlayground.
(* We will end NatPlayground to use the built-in definitions of naturals *)
Check (S O).
Check 1=2.

(* Definitions of Comparison Functions *)

Fixpoint eqb(n m : nat) : bool := 
  match n with 
  | O => match m with
          | O => true
          | S _ => false
         end
  | S n' => match m with
             | O => false
             | S m' => eqb n' m'
            end
  end.

Compute (eqb 1 2).

Fixpoint leb (n m : nat) : bool := 
  match n with 
  | O => true
  | S n' => match m with
             | O => false
             | S m' => leb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


(* What is the difference between x = y and x =? y? *)
(* They are fundamentally different! *)

(* ################################################################# *)
(** * Proof by Simplification *)
Theorem simpl_theorem: forall n : nat, 0 + n = n.
Proof. intros n'. reflexivity. Qed.

(* ################################################################# *)
(** * Proof by Rewriting *)
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof. intros. rewrite <- H. reflexivity. Qed. 

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof. intros n m o H1 H2. rewrite -> H1. rewrite <- H2. 
reflexivity. Qed.

(* ################################################################# *)
(** * Proof by Case Analysis *)
Theorem plus_1_neq_0 : forall n : nat,
  (leb n 5 = true) -> ((n + 1) =? 0 = false).
Proof.
  intros n.
  destruct n as [|n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  { destruct c eqn:Ec. 
    { reflexivity. }
    { reflexivity. } }
  { destruct c eqn:Ec.
    { reflexivity. }
    { reflexivity. } }
Qed.

(* ################################################################# *)
(** * Proof by Induction *)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof. Admitted.

(* Making local assertions *)
Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof. Admitted.




