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
Definition prod_curry {X Y Z : Type} 