(* Software Foundations Chapter 1 : Basics *)



(**************************************************
  Exercise: 1 star (nandb)
  Complete the definition of the following function, then make sure that the Example assertions below can each be verified by Coq.
**************************************************)
Definition nandb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => (negb b2)
    | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.



(**************************************************
  Exercise: 1 star (andb3)
  Do the same for the andb3 function below. This function should return true when all of its inputs are true, and false otherwise
**************************************************)

Definition andb3 (b1:bool) (b2:bool) (b3:bool) : bool :=
  match b1 with
    | true => match b2 with
                | true => match b3 with
                            | true => true 
                            | false => false
                          end
                | false => false
              end
    | false => false
end.

Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.



(**************************************************
Exercise: 1 star (factorial)
Recall the standard factorial function:
    factorial(0)  =  1 
    factorial(n)  =  n * factorial(n-1)     (if n>0)
Translate this into Coq.
**************************************************)

Fixpoint factorial (n:nat) : nat := 
  match n with
    | O => S O
    | S nn => mult n (factorial nn)
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.



(**************************************************
Exercise: 2 stars (blt_nat)
The blt_nat function tests natural numbers for less-than, yielding a boolean. Instead of making up a new Fixpoint for this one, define it in terms of a previously defined function.
Note: If you have trouble with the simpl tactic, try using compute, which is like simpl on steroids. However, there is a simple, elegant solution for which simpl suffices.
**************************************************)

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => beq_nat n' m'
            end
  end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.



(**************************************************
Exercise: 1 star (plus_id_exercise)
Remove "Admitted." and fill in the proof.
**************************************************)

Theorem plus_id_exercise : forall n m o : nat,
                             n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1. rewrite <- H2.
  reflexivity. 
Qed.



(**************************************************
Exercise: 2 stars (mult_S_1)
**************************************************)

Theorem mult_S_1 : forall n m : nat,
                     m = S n -> m * (1 + n) = m * m.
Proof.
  intros n m H.
  simpl. rewrite <- H. reflexivity. 
Qed.



(**************************************************
Exercise: 1 star (zero_nbeq_plus_1)
**************************************************)
Theorem zero_nbeq_plus_1 : forall n : nat,
                             beq_nat 0 (n + 1) = false.
Proof.
  intros n.
  destruct n.
  simpl. reflexivity. 
  simpl. reflexivity.
Qed.



(**************************************************
Exercise: 2 stars (boolean functions)
Use the tactics you have learned so far to prove the following theorem about boolean functions.
**************************************************)

Theorem identity_fn_applied_twice : forall (f : bool -> bool), 
                                      (forall (x : bool), f x = x) ->
                                      forall (b : bool), f (f b) = b.
Proof.
  intros f H1 b.
  rewrite H1. rewrite H1. reflexivity.
Qed.

  (*
    Now state and prove a theorem negation_fn_applied_twice similar to the previous one but where the second hypothesis says that the function f has the property that f x = negb x.
  *)

Theorem negb_involutive : forall b : bool,
                            negb (negb b) = b.
Proof.
  intros b. destruct b.
  reflexivity.
  reflexivity. 
Qed.

Theorem negation_fn_applied_twice : forall (f : bool -> bool),
                                      (forall (x : bool), f x = negb x) ->
                                      forall (b : bool), f (f b) = b.

Proof.
  intros f H1 b.
  rewrite H1. rewrite H1. rewrite negb_involutive. reflexivity.
Qed.


(**************************************************
  Exercise: 2 stars (andb_eq_orb)
  Prove the following theorem. (You may want to first prove a subsidiary lemma or two.)
**************************************************)
Theorem andb_eq_orb : forall (b c : bool),
                        (andb b c = orb b c) -> b = c.
Proof.
  intros b c.
  destruct b. destruct c.
  simpl. reflexivity.
  simpl. intro H. rewrite H. reflexivity.
  simpl. intro H. rewrite H. reflexivity. 
Qed.  



(**************************************************
  Exercise: 4 stars, recommended (binary)
  Consider a different, more efficient representation of natural numbers using a binary rather than unary system. That is, instead of saying that each natural number is either zero or the successor of a natural number, we can say that each binary number is either

    zero,
    twice a binary number, or
    one more than twice a binary number.

(a) First, write an inductive definition of the type bin corresponding to this 
description of binary numbers.
(Hint: recall that the definition of nat from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat → nat.
says nothing about what O and S "mean". It just says "O is a nat (whatever that is), and if n is a nat then so is S n". The interpretation of O as zero and S as 
successor/plus one comes from the way that we use nat values, by writing functions to do things with them, proving things about them, and so on. Your definition of bin should be correspondingly simple; it is the functions you will write next that will give it mathematical meaning.) *)

Inductive bin : Type :=
| inf : bin
| zero : bin -> bin
| one : bin -> bin.

(* (b) Next, write an increment function for binary numbers, and a function to convert binary numbers to unary numbers. *)

Fixpoint incbin (n : bin) : bin :=
match n with
| inf => one inf
| zero nn => one nn
| one nn => zero (incbin nn)
end.

Example incbin_test : incbin (one (one inf)) = zero (zero (one inf)).
Proof. reflexivity. Qed. 
  
Definition incnat (n : nat) : nat := S n.

Fixpoint bin_to_un (n : bin) : nat :=
match n with
| inf => O
| zero nn => mult 2 (bin_to_un nn)
| one nn => plus 1 (mult 2 (bin_to_un nn))
end.

Example test_bin_un1 : bin_to_un (zero (one (zero (one inf)))) = 10.
Proof. reflexivity. Qed.

Fixpoint un_to_bin (n : nat) : bin :=
match n with
| O => inf
| S nn => incbin (un_to_bin nn) 
end.

Example test_bin_un2 : un_to_bin 14 = zero (one (one (one inf))).
Proof. simpl. reflexivity. Qed. 

(* (c) Finally, prove that your increment and binary-to-unary functions commute: that is, incrementing a binary number and then converting it to unary yields the same result as first converting it to unary and then incrementing. *)

Theorem inc_un_comm : forall (m : bin),
                        bin_to_un (incbin m) = incnat (bin_to_un m).
Proof. 
  intro m. induction m as [|m1 |m2].
  reflexivity. 
  simpl. reflexivity.
  simpl. rewrite -> IHm2. unfold incnat. rewrite <- plus_n_Sm. 
  assert (H : S (bin_to_un m2) + bin_to_un m2 = bin_to_un m2 + S (bin_to_un m2)). 
   apply plus_comm. 
  rewrite -> H. rewrite <- plus_n_Sm. reflexivity. 
Qed. 



(**************************************************
  Exercise: 2 stars, optional (decreasing) 
  The requirement that some argument to each function be "decreasing" is a fundamental feature of Coq's design: In particular, it guarantees that every function that can be defined in Coq will terminate on all inputs. However, because Coq's "decreasing analysis" is not very sophisticated, it is sometimes necessary to write functions in slightly unnatural ways. To get a concrete sense of this, find a way to write a sensible Fixpoint definition (of a simple function on numbers, say) that does terminate on all inputs, but that Coq will not accept because of this restriction. 
**************************************************)

Fixpoint plus2 (n : nat) (m : nat) : nat :=
match (m, n) with 
| (O, O) => O
| (O, S(nn)) => nn
| (S(mm), O) => mm
| (S(mm), S(nn)) => S (S (plus nn mm))
end.

Example test_plus2 : (plus2 2 3) = 5.
Proof. simpl. reflexivity. Qed.
Eval simpl in (plus2 10 5).

(* Fixpoint plus3 (n : nat) (m : nat) : nat :=
match n with 
| O => m
| nn => plus3 (pred nn) (S m)
end. *)
