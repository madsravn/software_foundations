Add Rec LoadPath "~/dev/proofs".
Add Rec LoadPath "~/dev/proofs/sf".
Require Import lesson1.


Fixpoint factorial (n  : nat) : nat :=
match n with 
| O => S O
| S nn => mult n (factorial nn)
end.

Example test_factorial1 : (factorial 3) = 6.
Proof. reflexivity. Qed. 
Example test_factorial2 : (factorial 5) = (mult 10 12).
Proof. reflexivity. Qed. 

Theorem plus_id_example : forall n m : nat ,
                            n = m -> n + n = m + m.
Proof.
  intros n m H. rewrite -> H. reflexivity. 
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
                             beq_nat 0 (n + 1) = false.
Proof. 
  intros n. destruct n as [| nn].  
  simpl. reflexivity. 
  simpl. reflexivity. 
Qed. 

Theorem identity_fn_applied_twice : 
  forall f : bool -> bool,
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
(* for all boolean functions, if that function applied to some value is that value (is idempotent?)
 then that function applied twice is the same value. *)
Proof.
  intro f.
  intro H. 
  intro b. 
  rewrite -> H. 
  rewrite -> H. 
  reflexivity. 
Qed. 



Inductive bin : Type :=
| Q : bin (* zero *)
| W : bin -> bin (* twice bin *)
| E : bin -> bin. (* plus one bin *)

Require Export Basics.

Theorem mult_0_r : forall n : nat,
                     n * 0 = 0.
Proof. 
  intros n. 
  induction n as [| nn H].
  reflexivity. 
  simpl. apply H.
Qed.

Check plus_n_Sm.

Check plus_comm.

Check mult_comm.

Check bin.
 Check Q. 
Check W. 

Set Printing All. 
Unset Printing Notations.

(*
Definition inc (n : bin) :=
match n with 
| Q => W
| W nn => E (W nn)
| E nn => W nn
end.
*)



(* 
  zero = Q
  one = 
*) 

Require Import lesson2.
Require Import lesson3.

Print bool.
Print beq_nat.

Inductive foo : Type :=
| bar : foo
| baz : foo
| boo : foo.

(* guessing that the if statements only work for types that have two constructors
   but wanted to make sure *)

Definition thing_that_returns_foos (f : foo) := f.

(* doesnt work *)
*(* Eval simpl in (if (thing_that_returns_foos bar) then 1 else 2). *)


