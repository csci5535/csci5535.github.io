

From LF Require Export Induction.

(* ================================================================= *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).

Check doit3times.

(** The argument [f] here is itself a function (from [X] to
    [X]); the body of [doit3times] applies [f] three times to some
    value [n]. *)

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Definition minustwo (x:nat) : nat := x - 2.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.


(* List notation *)
Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
    
(** Filter function *)
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X := 
  match l with
  | [] => []
  | x::xs => (if test x then x::(filter test xs)
             else filter test xs)
  end.

Example test_filter1: filter even [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (List.length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Anonymous Functions *)

(* Write a function [filter_lt_10] that filters all numbers less than 
   10 from a given list list of numbers. *)


(* 
Example test_filter_lt_10 : filter_lt_10 [5;12;6;9;129] = [5;6;9].
Proof. Admitted.
*)
 

(* ================================================================= *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y.
Proof. Admitted.
(* Write a function [map_to_length] that maps a list of lists to list 
   of their lengths *)

(*   
Example test_map_to_length : 
  map_to_length [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = 
                      [2; 1; 1; 3; 0; 1].   
*)

(* ================================================================= *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Currying and Uncurrying *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.




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
Admitted.

(* Conditional hypothesis *)
Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
Admitted.

(* Quantified hypothesis *)
Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m)  ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof. Admitted.

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
Admitted.
