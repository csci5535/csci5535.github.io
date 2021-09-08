From LF Require Export Induction.

(* ================================================================= *)
(** ** Higher-Order Functions *)

(** Functions that manipulate other functions are often called
    _higher-order_ functions.  Here's a simple one: *)

Definition doit3times {X : Type} (f: X -> X) (x:X) : X :=
  f (f (f x)).

Check doit3times.

Check @doit3times.

Definition minustwo (x:nat) : nat := x - 2.

Example test_doit3times: doit3times minustwo 9 = 3.
(* minustwo (minustwo (minustwo 9) )*)
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
  | h :: t => if test h then h::(filter test t)
              else filter test t
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

Compute (filter (fun xs => List.length xs =? 1)
[ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]).    

(* ================================================================= *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | [] => []
  | h :: t => (f h)::(map f t)
  end.
(* Write a function [map_to_length] that maps a list of lists to list 
   of their lengths *)

Definition map_to_length {X:Type} (l : list (list X)) : list nat := 
  map (fun xs => List.length xs) l.

Example test_map_to_length : 
  map_to_length [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ] = 
                      [2; 1; 1; 3; 0; 1].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

(* 
   sum[2; 3; 4; 5]
   = sum [2; 3; 4] + 5
   = sum [2;3] + 4 + 5
   .. = 2 + 3 + 4 +5

   sum[2; 3; 4; 5]
   = 2 + sum [3;4;5]
   = 2 + 3 + sum [4;5]
   = ..
   = 2 + 3 + 4 +5
*)

Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | [] => b
  | h :: t => f h (fold f t b)
  end.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Check @fold.
Check fold mult.

(* ================================================================= *)
(** ** Currying and Uncurrying *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

