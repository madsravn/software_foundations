Add LoadPath "./sf".
Require Export Lists.
Require Import lesson3_Lists.



Module MumbleBaz.

(**************************************************
Exercise: 2 stars (mumble_grumble)
Consider the following two inductively defined types.
 **************************************************)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(* Which of the following are well-typed elements of grumble X for some type X? *)

  (* d (b a 5) - well-typed 
     Check d (b a 5).
     The term "b a 5" has type "mumble" while it is expected to have type "Type".
  *)

  (* d mumble (b a 5) - not well-typed (d only takes one argument and this argument must be an instance of the mumble type, not the mumble type itself).
*)
Check d mumble (b a 5).

  (* d bool (b a 5) - well-typed : d's first argument is the type we're parameterizing over; it takes in (b a 5) as a well-typed mumble and produces a bool grumble *)
Check d bool (b a 5).

(*   e bool true - well-typed *)
Check e bool true.

(*   e mumble (b c 0) - well-typed *)
Check e mumble (b c 0).

(*   e bool (b c 0) - not well-typed - first arg should be a bool, but is a mumble instead 
Check e bool (b c 0).
Error: The term "b c 0" has type "mumble" while it is expected to have type
 "bool".
*)

  (* c - well-typed *)
  Check c.



(**************************************************
  Exercise: 2 stars (baz_num_elts)
  Consider the following inductive definition:
 **************************************************)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(* How many elements does the type baz have? *)
(* Two  - each of the two ways you can make a type baz *)

End MumbleBaz.



(**************************************************
  Exercise: 2 stars, optional (poly_exercises)
  Here are a few simple exercises, just like ones in the Lists chapter, for practice with polymorphism. Fill in the definitions and complete the proofs below.
 **************************************************)

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
 (* can think of this like a function from types to inductive definition *)

Fixpoint length (X : Type) (l : list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length X t)
  end.

Fixpoint app (X : Type) (l1 l2 : list X)  : (list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end. 

Fixpoint snoc (X : Type) (l : list X) (n : X)  : (list X) :=
  match l with
    | nil => cons X n (nil X)
    | cons h t => cons X h (snoc X t n)
  end.

Fixpoint rev (X : Type) (l : list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Fixpoint repeat {X : Type} (n : X) (count : nat) : list X :=
  match count with
    | O => nil
    | S ct => cons n (repeat n ct)
  end.

Example test_repeat1: repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed. 

Notation "x :: y" := (cons x y)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                       (at level 60, right associativity).

Theorem nil_app : forall (X : Type),
                    forall (l : list X),
                      app [] l = l.
Proof. intros X l. reflexivity. Qed. 

Theorem rev_snoc : forall X : Type, 
                    forall v : X, 
                     forall s : list X,
                       rev (snoc s v) = v :: (rev s).
Proof. 
  intros X v s. induction s as [| h t].
  simpl. reflexivity. 
  simpl. rewrite -> IHt. simpl. reflexivity. 
Qed. 

Theorem cibele : forall Y : Type, 
                   forall l : list Y,
                    forall n : Y,
                      rev (snoc l n) = n :: (rev l).
Proof.
  intros Y l n. induction l as [| h t].
  simpl. reflexivity. 
  simpl. rewrite -> IHt. simpl. reflexivity. 
Qed.

Theorem rev_involutive : forall X : Type, 
                          forall l : list X, 
                            rev (rev l) = l.
Proof. 
 intros X l. induction l as [| h t].
 Case "l is empty".
 reflexivity. 
 Case "l is not empty".
 simpl. rewrite -> cibele. rewrite -> IHt. reflexivity. 
Qed. 

Theorem snoc_with_append : forall X : Type, 
                            forall l1 l2 : list X, 
                             forall v : X,
                               snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof. 
 intros X l1 l2 v. induction l1 as [| h t].
 simpl. reflexivity. 
 simpl. rewrite <- IHt.  reflexivity. 
Qed.

(**************************************************
  Exercise: 1 star, optional (combine_checks)
  Try answering the following questions on paper and checking your answers in coq:

  What is the type of combine (i.e., what does Check @combine print?)
  What does
    Eval compute in (combine [1;2] [false;false;true;true]).
  print? 
**************************************************)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match (lx, ly) with
    | ([],_)|(_,[]) => []
    | (x::tx, y:: ty) => (x,y) :: (combine tx ty)
  end.

(* type of combine? list X => list Y => list (X * Y) *)
Check @combine.
(* [(1, false), (2, false)] *)
Eval simpl in (combine [1;2] [false;false;true;true]).



(**************************************************
  Exercise: 2 stars (split)
  The function split is the right inverse of combine: it takes a list of pairs and returns a pair of lists. In many functional programing languages, this function is called unzip.

  Uncomment the material below and fill in the definition of split. Make sure it passes the given unit tests.
**************************************************)

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X * list Y) :=
  match l with 
    | nil => (nil, nil)
    | (hx, hy)::t => (hx::(fst (split t)), hy::(snd (split t)))
  end.

Example test_split: split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.



(**************************************************
  Exercise: 1 star, optional (hd_opt_poly)
  Complete the definition of a polymorphic version of the hd_opt function from the last chapter. Be sure that it passes the unit tests below.
**************************************************)

Definition hd_opt {X:Type} (l : list X) : option X :=
  match l with
    | nil => None
    | h::t => Some h
  end.

Check @hd_opt. 
Example test_hd_opt1 : hd_opt [1;2] = Some 1. 
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.



(**************************************************
  Exercise: 2 stars, advanced (currying)
  In Coq, a function f : A → B → C really has the type A → (B → C). That is, if you give f a value of type A, it will give you function f' : B → C. If you then give f' a value of type B, it will return a value of type C. This allows for partial application, as in plus3. Processing a list of arguments with functions that return functions is called currying, in honor of the logician Haskell Curry.

  Conversely, we can reinterpret the type A → B → C as (A * B) → C. This is called uncurrying. With an uncurried binary function, both arguments must be given at once as a pair; there is no partial application.
**************************************************)

(* We can define currying as follows: *)

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
  f (x,y).

(* As an exercise, define its inverse, prod_uncurry. Then prove the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).

(* Thought exercise: before running these commands, can you calculate the types of prod_curry and prod_uncurry? *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
                          prod_curry (prod_uncurry f) x y = f x y.
Proof. 
  intros X Y Z f x y. reflexivity.
Qed. 

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
                          prod_uncurry (prod_curry f) p = f p. 
Proof. 
  intros X Y Z f p. destruct p.
  assert (H1 : f (x,y) = prod_curry f x y). reflexivity. 
  rewrite -> H1. reflexivity. 
Qed.



(**************************************************
  Exercise: 2 stars (filter_even_gt7)
  Use filter (instead of Fixpoint) to write a Coq function filter_even_gt7 that takes a list of natural numbers as input and returns a list of just those that are even and greater than 7.
**************************************************)

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : (list X) :=
  match l with 
    | [] => []
    | h::t => if test h 
              then h :: (filter test t)
              else filter test t
  end.

Fixpoint geq_nat (n : nat) (m : nat) : bool :=
  match (n, m) with
    | (_,O) => true
    | (O,_) => false
    | (S nn, S mm) => geq_nat nn mm
  end.

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (geq_nat n 7)) (filter evenb l).

Eval simpl in (filter_even_gt7 [1;2;6;9;10;3;12;8]).

Example test_filter_even_gt7_1 :
 filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.   

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed. 



(**************************************************
  Exercise: 3 stars (partition)
  Use filter to write a Coq function partition:
    partition : ∀X : Type,
                (X → bool) → list X → list X * list X
  Given a set X, a test function of type X → bool and a list X, partition should return a pair of lists. The first member of the pair is the sublist of the original list containing the elements that satisfy the test, and the second is the sublist containing those that fail the test. The order of elements in the two sublists should be the same as their order in the original list.
**************************************************)

Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Definition oddb (n : nat) := negb (evenb n).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed. 

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed. 



(**************************************************
  Exercise: 3 stars (map_rev)
  Show that map and rev commute. You may need to define an auxiliary lemma.
 **************************************************)

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : (list Y) :=
match l with
| [] => []
| h::t => (f h)::(map f t)
end.

Theorem map_snoc : forall (X Y : Type) (f : X -> Y) (l : list X) (n : X),
                     snoc (map f l) (f n) = map f (snoc l n).
Proof.
  intros X Y f l n. induction l as [|h t].
  simpl. reflexivity.
  simpl. rewrite -> IHt.
  reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
                    map f (rev l) = rev (map f l).
Proof.
 intros X Y f l.
 induction l as [| h t].
 Case "l is empty".
 simpl. reflexivity.
 Case "l is not empty".
 simpl. rewrite <- IHt.
 rewrite -> map_snoc.
 reflexivity.
Qed.



(**************************************************
  Exercise: 2 stars (flat_map)
  The function map maps a list X to a list Y using a function of type X → Y. We can define a similar function, flat_map, which maps a list X to a list Y using a function f of type X → list Y. Your definition should work by 'flattening' the results of f, like so:
        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
 **************************************************)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1: flat_map (fun n => [n;n;n]) [1;5;4] = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed. 



(**************************************************
  Exercise: 2 stars, optional (implicit_args)
  The definitions and uses of filter and map use implicit arguments in many places. Replace the curly braces around the implicit arguments with parentheses, and then fill in explicit type parameters where necessary and use Coq to check that you've done so correctly. (This exercise is not to be turned in; it is probably easiest to do it on a copy of this file that you can throw away afterwards.)
**************************************************)

(* skipped *)



(**************************************************
  Exercise: 1 star, optional (fold_types_different)
  Observe that the type of fold is parameterized by two type variables, X and Y, and the parameter f is a binary operator that takes an X and a Y and returns a Y. Can you think of a situation where it would be useful for X and Y to be different? 
 **************************************************)

(* When we want to perform an operation on (like a map) before aggregating. e.g.: *)



(**************************************************
  Exercise: 1 star (override_example)
  Before starting to work on the following proof, make sure you understand exactly what the theorem is saying and can paraphrase it in your own words. The proof itself is straightforward.
 **************************************************)

Definition override {X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat) => if beq_nat k k' then x else f k'.

Definition constfun {X : Type} (x : X) : nat -> X :=
 fun (k : nat) => x.

Theorem override_example :  forall (b:bool), 
  (override (constfun b) 3 true) 2 = b.
Proof. intros b. destruct b. reflexivity. reflexivity. Qed. 



(**************************************************
  Exercise: 2 stars (override_neq)
**************************************************) 

Theorem override_neq : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
                         f k1 = x1 -> 
                          beq_nat k2 k1 = false -> 
                           (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H1 H2.
  unfold override.
  rewrite -> H2.
  rewrite -> H1.
  reflexivity.
Qed.



(**************************************************
  Exercise: 2 stars (fold_length)
  Many common functions on lists can be implemented in terms of fold. For example, here is an alternative definition of length:
**************************************************)

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
match l with
| nil => b
| h::t => f h (fold f t b)
end.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(* Prove the correctness of fold_length.*)

Theorem fold_length_correct : forall X (l : list X),
                                fold_length l = length l.
Proof.
  intros X l. induction l as [|h t]. 
  Case "the list is empty".
  simpl. compute. reflexivity.
  Case "the list is not empty".
  simpl. 
  rewrite <- IHt.
  unfold fold_length.
  simpl.
  reflexivity.
Qed.



(**************************************************
  Exercise: 3 stars (fold_map)
  We can also define map in terms of fold. Finish fold_map below.
 **************************************************)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => (f x)::y) l [].

Example fold_map_test1 : fold_map S [1;2;3] = [2;3;4].
Proof. compute. reflexivity. Qed.

(* Write down a theorem in Coq stating that fold_map is correct, and prove it. *)

Theorem fold_map_correct : forall X Y (f : X -> Y) (l : list X),
                             fold_map f l = map f l.
Proof. 
  intros X Y f l. induction l as [|h t].
  Case "l is empty".
  simpl. compute. reflexivity.
  Case "l is not empty".
  simpl. 
  rewrite <- IHt. 
  unfold fold_map.
  simpl.
  reflexivity.
Qed.