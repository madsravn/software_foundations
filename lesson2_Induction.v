(* Software Foundations Chapter 2 : Induction *)
Require Export Basics.
Require Import lesson1_Basics.

Module Lesson2.
(**************************************************
  Exercise: 2 stars (andb_true_elim2)
  Prove andb_true_elim2, marking cases (and subcases) when you use destruct.
**************************************************)

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Theorem andb_true_elim2 : forall b c : bool,
                            andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b. destruct c.
  Case "both true".
  simpl. reflexivity.
  Case "true false".
  simpl. intro H. rewrite H. reflexivity. 
  destruct c.
  Case "false true".
  simpl. intro H. reflexivity. 
  Case "both false".
  simpl. intro H. rewrite H. reflexivity. 
Qed.



(**************************************************
Exercise: 2 stars (basic_induction)
Prove the following lemmas using induction. You might need previously proven results.
**************************************************)

Theorem mult_0_r : forall n : nat,
                     n * 0 = 0.
Proof.
  intros n.
  induction n as [|nn].
  simpl. reflexivity.
  simpl. rewrite -> IHnn. reflexivity. 
Qed.

Check Lesson1.plus_n_Sm. 
Check Lesson1.plus_comm.
(* defined in lesson1_Basics - left over from the older SF ordering and used 
   in the binary problem 
*)

Theorem plus_assoc : forall n m p : nat,
                       n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| nn].
  simpl. reflexivity.
  simpl. rewrite -> IHnn. reflexivity.
Qed.



(**************************************************
  Exercise: 2 stars (double_plus)
  Consider the following function, which doubles its argument:
 **************************************************)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
              
(* Use induction to prove this simple fact about double: *)

Lemma double_plus : forall n, 
                      double n = n + n .
Proof.
  intros n. induction n as [|nn].
  simpl. reflexivity.
  simpl. rewrite -> IHnn.
  rewrite -> plus_n_Sm. reflexivity.
Qed.



(**************************************************
  Exercise: 1 star (destruct_induction)
  Briefly explain the difference between the tactics destruct and induction.
 **************************************************)

(* Destruct decomposes its argument into a finite number of constructors.
   Induction decomposes its argument into a base case and a recursive
   definition. It can be used over potentially infinite sets, so long as 
   those sets are countable.
*)



(************************************************
  Exercise: 4 stars (mult_comm)
  Use assert to help prove this theorem. You shouldn't need to use induction.
 ************************************************)
Theorem plus_swap : forall n m p : nat, 
                      n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  assert(H1 : m + n = n + m). 
   rewrite -> Lesson1.plus_comm. reflexivity.
  rewrite <- H1. reflexivity.
Qed. 

(*Now prove commutativity of multiplication. (You will probably need to define and prove a separate subsidiary theorem to be used in the proof of this one.) You may find that plus_swap comes in handy.
*)

Theorem mult_m_Sn : forall n m,
                      m * S n = m * n + m.
Proof.
  intros foo bar. induction bar as [| barf].
  Case "base case".
  simpl. reflexivity. 
  Case "inductive case".
  simpl.
  rewrite -> IHbarf. 
  rewrite -> plus_assoc. 
  rewrite <- plus_n_Sm. 
  reflexivity.
Qed.

Theorem add_comm_mult : forall n m p,
                          n + m * p = m * p + n.
Proof.
  intros n m p. induction n as [| nn].
  simpl. rewrite -> Lesson1.plus_0_r. reflexivity. 
  simpl. rewrite -> IHnn. rewrite -> plus_n_Sm. reflexivity. 
Qed.  

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n. induction n as [| nn].
  Case "base case".
  simpl. rewrite -> mult_0_r. reflexivity. 
  Case "inductive case".
  simpl. rewrite <- IHnn.
  rewrite -> mult_m_Sn. rewrite -> add_comm_mult. reflexivity. 
Qed.



(**************************************************
Exercise: 2 stars, optional (evenb_n__oddb_Sn)
Prove the following simple fact:
**************************************************)

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S nn) => evenb nn
  end.

Theorem evenb_n__oddb_Sn :  forall n : nat,
                              evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [|nn].
  Case "base case : n is zero".
  simpl. reflexivity.
  Case "inductive case : n is some natural number".
  assert (evens : forall (a : nat), evenb a = evenb (S (S a))).
   destruct a.
   simpl. reflexivity.
   simpl. reflexivity.
  rewrite <- evens.
  assert (add_neg : evenb (S nn) = negb (negb (evenb (S nn)))).
   rewrite -> Lesson1.negb_involutive. reflexivity.
  rewrite -> add_neg.
  rewrite <- IHnn.
  reflexivity.
Qed.  



(**************************************************
  Exercise: 3 stars, optional (more_exercises)
  Take a piece of paper. For each of the following theorems, first think about whether (a) it can be proved using only simplification and rewriting, (b) it also requires case analysis (destruct), or (c) it also requires induction. Write down your prediction. Then fill in the proof. (There is no need to turn in your piece of paper; this is just to encourage you to reflect before hacking!)
**************************************************)

Theorem ble_nat_refl : forall n:nat,
  true = Lesson1.ble_nat n n.
Proof.
  intros n. induction n as [|nn]. 
  simpl. reflexivity.
  simpl. rewrite <- IHnn. reflexivity. 
Qed.

Theorem zero_nbeq_S :  forall n:nat,
  Lesson1.beq_nat 0 (S n) = false.
Proof. intros n. simpl. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  simpl. reflexivity. 
  simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l :  forall n m p : nat,
  Lesson1.ble_nat n m = true -> Lesson1.ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p. induction p as [| pp].
  simpl. induction n as [| nn]. 
  Theorem zero_ble_S : forall n : nat,
    Lesson1.ble_nat 0 n = true.
  Proof.
    intros n. induction n as [| nn]. 
    simpl. reflexivity. 
    simpl. reflexivity. 
  Qed. 
  rewrite -> zero_ble_S. reflexivity.
  destruct (Lesson1.ble_nat (S nn) m). reflexivity. 
  intro H. rewrite <- H. reflexivity. 
  simpl. intro H. rewrite <- IHpp. 
  reflexivity. rewrite -> H. reflexivity. 
Qed.

Theorem S_nbeq_0 : forall n:nat,
  Lesson1.beq_nat (S n) 0 = false.
Proof. intros n. simpl. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof. intros n. simpl. rewrite -> Lesson1.plus_0_r. reflexivity. Qed.

Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
 intros b c. destruct b. destruct c. 
 simpl. reflexivity. 
 simpl. reflexivity. 
 simpl. reflexivity. 
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
 intros n m p. induction n as [|nn].
 simpl. reflexivity. 
 simpl. rewrite -> add_comm_mult. rewrite -> IHnn. 
 rewrite <- Lesson1.plus_comm. rewrite <- plus_assoc.
 reflexivity. 
Qed.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
 intros n m p. induction n as [| nn]. 
 simpl. reflexivity.
 simpl. rewrite -> mult_plus_distr_r. rewrite -> IHnn. reflexivity. 
Qed.

(**************************************************
  Exercise: 2 stars, optional (beq_nat_refl)
  Prove the following theorem. Putting true on the left-hand side of the equality may seem odd, but this is how the theorem is stated in the standard library, so we follow suit. Since rewriting works equally well in either direction, we will have no problem using the theorem no matter which way we state it.
**************************************************)
Theorem beq_nat_refl : forall n : nat, 
                         true = Lesson1.beq_nat n n.
Proof.
  intros n. induction n as [|nn].
  Case "n is zero".
  simpl. reflexivity.
  Case "n is some natural number".
  simpl. rewrite <- IHnn. reflexivity.
Qed.



(**************************************************
  Exercise: 2 stars, optional (plus_swap')
  The replace tactic allows you to specify a particular subterm to rewrite and what you want it rewritten to. More precisely, replace (t) with (u) replaces (all copies of) expression t in the goal by expression u, and generates t = u as an additional subgoal. This is often useful when a plain rewrite acts on the wrong part of the goal.

  Use the replace tactic to do a proof of plus_swap', just like plus_swap but without needing assert (n + m = m + n).
**************************************************)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. 
  rewrite <- Lesson1.plus_comm. 
  replace (n + p) with (p + n). 
  rewrite -> plus_assoc. reflexivity. 
  rewrite -> Lesson1.plus_comm. reflexivity. 
Qed.

(**************************************************
  Exercise: 3 stars (binary_commute)
  Recall the increment and binary-to-unary functions that you wrote for the binary exercise in the Basics chapter. Prove that these functions commute — that is, incrementing a binary number and then converting it to unary yields the same result as first converting it to unary and then incrementing.

(Before you start working on this exercise, please copy the definitions from your solution to the binary exercise here so that this file can be graded on its own. If you find yourself wanting to change your original definitions to make the property easier to prove, feel free to do so.)
**************************************************)

Check Lesson1.inc_un_comm.



(**************************************************
  Exercise: 5 stars, advanced (binary_inverse) 
  This exercise is a continuation of the previous exercise about binary numbers. You will need your definitions and theorems from the previous exercise to complete this one.
**************************************************)

(* (a) First, write a function to convert natural numbers to binary numbers. Then prove that starting with any natural number, converting to binary, then converting back yields the same natural number you started with. *)

Check Lesson1.un_to_bin.

Theorem incbin_un : forall b, 
                      Lesson1.bin_to_un (Lesson1.incbin b) = S (Lesson1.bin_to_un b).
Proof.
  intros b. induction b as [|zero|one].
  simpl. reflexivity.
  simpl. reflexivity. 
  simpl. rewrite -> IHone. simpl. rewrite <- plus_n_Sm. reflexivity. 
Qed. 

Theorem nat_to_bin_back : forall n : nat,
                            Lesson1.bin_to_un (Lesson1.un_to_bin n) = n.
Proof. 
  intro n. induction n as [|nn].
  simpl. reflexivity.
  simpl. rewrite -> incbin_un. rewrite -> IHnn. reflexivity. 
Qed. 

(* (b) You might naturally think that we should also prove the opposite direction: that starting with a binary number, converting to a natural, and then back to binary yields the same number we started with. However, it is not true! Explain what the problem is. *)

(* Having problems with the base case, since there are "two ways" to represent zero *)

Fixpoint all_zeroes (b : Lesson1.bin) : bool :=
  match b with
    | Lesson1.inf => true
    | Lesson1.one bb => false
    | Lesson1.zero bb => all_zeroes bb
  end.

Definition elim_zeroes (b : Lesson1.bin) : Lesson1.bin :=
  match all_zeroes b with
    | true => Lesson1.inf
    | false => b
  end.

(* redefining un_to_bin *)

Fixpoint un_to_bin (n : nat) : Lesson1.bin :=
  elim_zeroes (match n with
                 | O => Lesson1.inf
                 | S nn => Lesson1.incbin (Lesson1.un_to_bin nn) 
               end).

(* Fixpoint plus_bin (b1 : Lesson1.bin) (b2 : Lesson1.bin) (carry : bool) : Lesson1.bin := *)
(*   match b1 with *)
(*     | Lesson1.inf => match b2 with *)
(*                        | Lesson1.inf => if carry  *)
(*                                         then Lesson1.one Lesson1.inf  *)
(*                                         else Lesson1.zero Lesson1.inf *)
(*                        | _ => if carry  *)
(*                               then Lesson1.one b2  *)
(*                               else b2 *)
(*                      end *)
(*     | Lesson1.zero n => match b2 with *)
(*                           | Lesson1.inf => b1 *)
(*                           | Lesson1.zero m => if carry  *)
(*                                               then Lesson1.one (plus_bin n m false)  *)
(*                                               else Lesson1.zero (plus_bin n m true) *)
(*                           | Lesson1.one m => if carry  *)
(*                                              then Lesson1.zero (plus_bin n m true)  *)
(*                                              else Lesson1.one (plus_bin n m false) *)
(*                         end *)
(*     | Lesson1.one n => match b2 with *)
(*                          | inf => if carry  *)
(*                                   then Lesson1.one b1  *)
(*                                   else b1 *)
(*                          | Lesson1.zero m => if carry  *)
(*                                              then Lesson1.zero (plus_bin n m true)  *)
(*                                              else Lesson1.one (plus_bin n m false) *)
(*                          | Lesson1.one m => if carry  *)
(*                                             then Lesson1.one (plus_bin n m true)  *)
(*                                             else Lesson1.zero (plus_bin n m true) *)
(*                        end *)
(*   end. *)

(* Notation "x +b y" := (plus_bin x y false) (at level 50, left associativity) : nat_scope.  *)

(* Example plus_bin_test1 : (un_to_bin 5) +b (un_to_bin 7) = (un_to_bin 12). *)
(* Proof. simpl. reflexivity. Qed.  *)
(* Example plus_bin_test2 : (un_to_bin 8) +b (un_to_bin 3) = (un_to_bin 11). *)
(* Proof. simpl. reflexivity. Qed. *)


(* Lemma double_zero : forall (n : nat), *)
(*                       elim_zeroes (Lesson1.un_to_bin (double n)) = elim_zeroes (Lesson1.zero (Lesson1.un_to_bin n)). *)
(* Proof. *)
(*   intro n. induction n as [|nn]. *)
(*   simpl. compute. reflexivity. *)
(*   simpl.  *)

(* Theorem bin_to_nat_back : forall b : Lesson1.bin, *)
(*                             un_to_bin (Lesson1.bin_to_un b) = b.  *)
(* Proof.  *)
(*   intro b. induction b as [|n|m]. *)
(*   Case "inf". simpl. reflexivity.  *)
(*   Case "zero".  *)
(*   simpl. *)
(*   rewrite -> Lesson1.plus_0_r. *)
(*   rewrite <- double_plus. *)
  
(* I'm going to guess that this has something to do with how you don't know where the zero in a binary 
number comes from? Like, it could come from adding two zeros or it could come from adding two ones? 
Maybe this makes the structure difficult for using induction? *)

(* (c) Define a function normalize from binary numbers to binary numbers such that for any binary number b, converting to a natural and then back to binary yields (normalize b). Prove it.

Again, feel free to change your earlier definitions if this helps here. 
*)

Fixpoint contains_ones (b : Lesson1.bin) :=
  match b with
    | Lesson1.inf => false
    | Lesson1.one bb => true
    | Lesson1.zero bb => contains_ones bb
  end.

Definition normalize (b : Lesson1.bin) : Lesson1.bin := 
  if (Lesson1.beq_nat (Lesson1.bin_to_un b) 0) then Lesson1.inf else b.

Definition plus_bin (b1 b2 : Lesson1.bin) : Lesson1.bin :=
  Lesson1.un_to_bin (Lesson1.bin_to_un b1 + (Lesson1.bin_to_un b2)).

Theorem zero_double : forall (z : Lesson1.bin),
                        Lesson1.bin_to_un (Lesson1.zero z) = double (Lesson1.bin_to_un z).
Proof.
  intro z. induction z as [|zz|zz].
  Case "z is inf".
   simpl. 
   reflexivity.
  Case "z is some (zero zz)".
   simpl. 
   rewrite -> Lesson1.plus_0_r.
   rewrite -> Lesson1.plus_0_r.
   rewrite -> double_plus.
   reflexivity.
  Case "z is some (one zz)".
   simpl. 
   rewrite -> Lesson1.plus_0_r.
   rewrite -> Lesson1.plus_0_r.
   rewrite -> double_plus.
   rewrite <- plus_n_Sm.
   reflexivity.
Qed.

Theorem normalize_implies : forall (a b : Lesson1.bin),
                              a = b -> normalize a = normalize b.
Proof.
  intros a b H.
  rewrite H.
  reflexivity.
Qed.

Theorem one_S : forall (z : Lesson1.bin),
                  Lesson1.bin_to_un (Lesson1.one z) = S (double (Lesson1.bin_to_un z)).
Proof.
  intros z. induction z as [|zz|zz].
  Case "z is inf".
  simpl.
  reflexivity.
  Case "z is some (zero zz)".
  simpl.
  rewrite -> Lesson1.plus_0_r.
  rewrite -> Lesson1.plus_0_r.
  rewrite -> double_plus.
  reflexivity.
  Case "z is some (one zz)".
  simpl.
  rewrite -> Lesson1.plus_0_r.
  rewrite -> Lesson1.plus_0_r.
  rewrite -> double_plus.
  rewrite -> plus_assoc.
  rewrite <- plus_n_Sm.
  rewrite -> plus_assoc.
  reflexivity.
Qed.


Theorem double_zero : forall (n : nat),
                        Lesson1.un_to_bin (double n) = normalize (Lesson1.zero (Lesson1.un_to_bin n)).
Proof. 
  intros n.
  induction n as [|nn].
  Case "base case : n is zero".
  simpl.
  reflexivity.
  Case "inductive case : n is S nn".
  simpl.
  SCase "show bin version of (b + 1) * 2 = 2*b + 2 
                                           i.e. zero (incbin b) = incbin (incbin (zero b))".
  assert (plus_one_times_two : forall b,
                Lesson1.zero (Lesson1.incbin b) = Lesson1.incbin (Lesson1.incbin (Lesson1.zero b))).
   intros b.
   simpl.
   reflexivity.
  rewrite -> plus_one_times_two.
  SSCase "show that any number greater than zero normalized is normalized to itself".
  assert (norm_same : forall b,
                        normalize (Lesson1.incbin b) = Lesson1.incbin b).
   intros b. induction b as [|bb|bb].
   simpl. compute. reflexivity.
   simpl. compute. reflexivity.
   simpl. 
   



  Theorem S_one : forall (n : nat),
                    Lesson1.un_to_bin (S (double n)) = Lesson1.one (Lesson1.un_to_bin (double n)).

Theorem normalized : forall (b : Lesson1.bin),
                       Lesson1.un_to_bin (Lesson1.bin_to_un (normalize b)) = (normalize b).
Proof.
  intros b. induction (normalize b) as [i|z|o].
  Case "bin is inf".
  simpl. reflexivity.
  Case "bin is an even number".
  rewrite -> zero_double.
  rewrite -> double_zero.
  rewrite -> IHz.
  reflexivity.
  Case "bin is an odd number".
  rewrite -> one_S.