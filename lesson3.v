(* Require Export Lists.*)

Inductive list (X : Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
 (* can think of this like a function from types to inductive definition *)

Check nil. 
Check cons. 
Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X : Type) (l : list X) : nat :=
match l with
| nil => 0
| cons h t => S (length X t)
end.
(* note that we don't need the type for this cons -> it's inferred from the definition of the list *)
Example test_length1 :
 length nat (cons nat 1 (cons nat 2 (nil nat))) = 2. 
Proof. reflexivity. Qed. 

Fixpoint app (X : Type) (l1 l2 : list X)  : (list X) :=
match l1 with
| nil => l2
| cons h t => cons X h (app X t l2)
end. 

Definition snoc' (X : Type) (l : list X) (n : X) : (list X) := app X l (cons X n (nil X)).
Fixpoint snoc (X : Type) (l : list X) (n : X)  : (list X) :=
match l with
| nil => cons X n (nil X)
| cons h t => cons X h (snoc X t n)
end.

Example test_snoc1 : snoc bool (nil bool) true = cons bool true (nil bool).
Proof. reflexivity. Qed.
Example test_snoc2 : snoc bool (cons bool true (cons bool false (nil bool))) false = (cons bool true (cons bool false (cons bool false (nil bool)))).
Proof. reflexivity. Qed. 

Fixpoint rev (X : Type) (l : list X) : list X :=
match l with
| nil => nil X
| cons h t => snoc X (rev X t) h
end.

Fixpoint app' X l1 l2 : list X :=
match l1 with
| nil => l2
| cons h t => cons X h (app' X t l2)
end.

Check app'.
Check app.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(* declare args to be implicit *)
Fixpoint length'' {X : Type} (l : list X) : nat :=
match l with
| nil => 0
| cons h t => S (length'' t)
end.

(* sometimes there isn't enough type information *)
(* e.g. 
   Definition mylist := nil.
   instead write: *)
Definition mylist : list nat := nil.
Check @nil. 
(* for a one-off explicit type argument *)
Definition mynil := @nil nat. 
Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity). 

Definition list123''' := [1,2,3].

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
match count with
| O => nil 
| S ct => cons n (repeat X n ct)
end.

Example test_repeat1: repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed. 

Theorem nil_app : forall X : Type, forall l : list X,
  app [] l = l.
Proof. 
  intros X l. reflexivity. Qed. 

Theorem rev_snoc : forall X : Type, forall v : X, forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof. 
  intros X v s. 
  induction s as [| h t].
  simpl. reflexivity. 
  simpl. rewrite -> IHt. simpl. reflexivity. 
Qed. 
 (* email cibele about how doing this with the other definition of snoc makes the proof a lot harder *)

Theorem rev_involutive : forall X : Type, forall l : list X, 
 rev (rev l) = l.
Proof. 
 intros X l. 
 induction l as [| h t].
 reflexivity. 
 simpl. 
 Theorem cibele : forall Y : Type, forall l : list Y, forall n : Y,
   rev (snoc l n) = n :: (rev l).
  Proof.
    intros Y l n. 
    induction l as [| h t].
    simpl. reflexivity. 
    simpl. rewrite -> IHt. simpl. reflexivity. 
  Qed.
 rewrite -> cibele. rewrite -> IHt. reflexivity. 
Qed. 

Theorem snoc_with_append : forall X : Type, forall l1 l2 : list X, forall v : X,
 snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof. 
 intros X l1 l2 v. 
 induction l1 as [| h t].
 simpl. reflexivity. 
 simpl. rewrite <- IHt.  reflexivity. 
Qed.

Inductive prod (X Y : Type) : Type :=
pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope. 

Definition fst {X Y : Type} (p : X * Y) : X :=
 match p with (x, y) => x
end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
 match p with (x, y) => y
end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
match (lx, ly) with
| ([],_)|(_,[]) => []
| (x::tx, y:: ty) => (x,y) :: (combine tx ty)
end.

(* type of combine? list X => list Y => list (X * Y) *)
Check @combine.
(* [(1, false), (2, false)] *)
Eval simpl in (combine [1,2] [false, false, true, true]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X * list Y) :=
match l with 
| nil => (nil, nil)
| (hx, hy)::t => (hx::(fst (split t)), hy::(snd (split t)))
end.

Example test_split: split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity. Qed.

Inductive option (X: Type) : Type :=
| Some : X -> option X
| None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint beq_nat (n : nat) (m : nat) : bool :=
match (n,m) with
| (O,O) => true
| (_,O) | (O,_) => false
| (S nn, S mm) => beq_nat nn mm
end.

Fixpoint index {X:Type} (n : nat) (l : list X) : option X :=
match l with 
| [] => None
| a :: ll => if beq_nat n 0 then Some a else index (pred n) ll
end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed. 

Definition hd_opt {X:Type} (l : list X) : option X :=
match l with
| nil => None
| h::t => Some h
end.

Check @hd_opt. 
Example test_hd_opt1 : hd_opt [1,2] = Some 1. 
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1],[2]] = Some [1].
Proof. reflexivity. Qed.

(* HIGHER ORDER FUNCTIONS *)
Definition doit3times {X : Type} (f : X -> X) (n : X) : X := f (f (f n)).
Check @doit3times. 
Example test_doit3times : doit3times pred 9 = 6.
Proof. reflexivity. Qed.
Example test_doit3times' : doit3times negb true = false.
Proof. reflexivity. Qed. 

(* CURRYING *)
Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z :=
 f (x,y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z :=
 f (fst p) (snd p).

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
 intros X Y Z f p. 
 destruct p.
 assert (H1 : f (x,y) = prod_curry f x y). 
  reflexivity. 
 rewrite -> H1. 
  reflexivity. 
Qed.


Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : (list X) :=
 match l with
 | [] => []
 | h::t => if test h 
           then h :: (filter test t)
           else filter test t
end.

Fixpoint evenb (n : nat) :=
match n with
| O => true
| S O => false
| S (S nn) => evenb nn
end.

Example test_filter1 : filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
 beq_nat (length l) 1. 

Example test_filter2 : filter length_is_1 [[1,2],[3],[4],[5,6,7],[],[8]] = [[3],[4],[8]].
Proof. reflexivity. Qed.

Example test_filter2' : filter (fun l => beq_nat (length l) 1) [[1,2],[3],[4],[5,6,7],[],[8]] = [[3],[4],[8]].
Proof. reflexivity. Qed.

Fixpoint geq_nat (n : nat) (m : nat) :=
match n,m with
| O, O | _, O => true
| O, _  => false
| S nn, S mm => geq_nat nn mm
end.

Definition filter_even_gt7 (l : list nat) : list nat :=
 filter (fun n => (geq_nat n 7)) (filter evenb l).

Eval simpl in (filter_even_gt7 [1,2,6,9,10,3,12,8]).

Example test_filter_even_gt7_1 :
 filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.   

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed. 

Definition partition {X : Type} (test : X -> bool) (l : list X) 
                     : list X * list X :=
(filter test l, filter (fun x => negb (test x)) l).

Definition oddb (n : nat) := negb (evenb n).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed. 

Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed. 

Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : (list Y) :=
match l with
| [] => []
| h::t => (f h)::(map f t)
end.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
 map f (rev l) = rev (map f l).
Proof.
 intros X Y f l.
 induction l as [| h t].
 simpl. reflexivity.
 simpl. rewrite <- IHt.
Admitted.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : (list Y) :=
 match l with
 | [] => []
 | h :: t => (f h) ++ (flat_map f t)
end.

Example test_flat_map1: 
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed. 

Definition option_map {X Y: Type} (f : X -> Y) (xo : option X) : option Y :=
match xo with
| None => None
| Some x => Some (f x)
end.

Fixpoint filter' (X : Type) (f : X -> bool) (l : list X) :=
match l with
| [] => []
| h :: t => if (f h)
            then h::(filter' X f t)
            else filter' X f t
end.

Fixpoint map' (X  Y : Type) (f : X -> Y) (l : list X) :=
match l with
| [] => []
| h::t => (f h)::(map' X Y f t)
end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
match l with
| nil => b
| h::t => f h (fold f t b)
end.

(* Exercise: 1 star, optional (fold_types_different)
Observe that the type of fold is parameterized by two type 
variables, X and Y, and the parameter f is a binary operator that 
takes an X and a Y and returns a Y. Can you think of a situation 
where it would be useful for X and Y to be different? *)

(* When we want to perform an operation on (like a map) before aggregating. e.g.: *)

Definition all_evens (l : list nat) :=
 fold (fun n b => andb b (evenb n)) l true.

Example all_evens_test1 : all_evens [0,2,4] = true.
Proof.  reflexivity. Qed.
Example all_evens_test2 : all_evens [] = true.
Proof. reflexivity. Qed.
Example all_evens_test3 : all_evens [2,4,5,8] = false.
Proof. reflexivity. Qed. 

Definition constfun {X : Type} (x : X) : nat -> X :=
 fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X : Type} (f : nat -> X) (k : nat) (x : X) : nat -> X :=
 fun (k' : nat) => if beq_nat k k' then x else f k'.

(* Exercise: 1 star (override_example)
Before starting to work on the following proof, make sure you 
understand exactly what the theorem is saying and can paraphrase 
it in your own words. The proof itself is straightforward. *)

Theorem override_example :  forall (b:bool), 
  (override (constfun b) 3 true) 2 = b.
Proof.
 intros b. 
 destruct b.
 reflexivity. 
 reflexivity. 
Qed. 

Inductive boolllist : nat -> Type :=
 boollnil : boolllist 0
| boollcons : forall n, bool -> boolllist n -> boolllist (S n).

Implicit Arguments boollcons [[n]].

Check (boollcons true (boollcons false (boollcons true boollnil))).

Fixpoint blapp {n1} (l1 : boolllist n1)
               {n2} (l2 : boolllist n2)
               : boolllist (n1 + n2) :=
match l1 with
| boollnil => l2
| boollcons _ h t => boollcons h (blapp t l2)
end.

Inductive llist (X : Type) : nat -> Type :=
  lnil : llist X 0
| lcons : forall n, X -> llist X n -> llist X (S n).

Implicit Arguments lnil [[X]].
Implicit Arguments lcons [[X] [n]].

Check (lcons true (lcons false (lcons true lnil))).

Fixpoint lapp (X : Type)
              {n1} (l1 : llist X n1)
              {n2} (l2 : llist X n2)
              : llist X (n1 + n2) :=
match l1 with
| lnil => l2
| lcons _ h t => lcons h (lapp X t l2)
end.

