(* asdf *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  |saturday : day
  | sunday : day.
               
Definition next_weekday (d:day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday 
    | wednesday => thursday
    | thursday => friday
    | friday => monday 
    | saturday => monday
    | sunday => monday
  end.

Eval simpl in (next_weekday friday).

Eval simpl in (next_weekday (next_weekday saturday)).

Example test_next_weekday:
(next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b:bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with 
    | true => b2
    | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example text_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Definition admit {T: Type} : T. Admitted.

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

Definition pred (n : nat) : nat :=
match n with
| O => O
| S(nn) => nn
end.

Fixpoint evenb (n : nat) : bool :=
match n with
| O => true
| S O => false
| S(S(nn)) => evenb(nn)
end.

Example even_test1 : (evenb 0) = true.
Proof. simpl. reflexivity. Qed.
Example even_test2: (evenb 1) = false.
Proof. simpl. reflexivity. Qed.
Example even_test3 : (evenb 2) = true.
Proof. simpl. reflexivity. Qed. 

Fixpoint oddb (n : nat) : bool := negb (evenb n).

Fixpoint plus (n : nat) (m : nat) : nat :=
match n with
| O => m
| S(nn) => S (plus nn m)
end.

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

(* Exercise: 4 stars, recommended (mult_comm)
Use assert to help prove this theorem. 
You shouldn't need to use induction. *)

Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.

Theorem assoc_add : forall n m p : nat,
  (n + m) + p = n + (m + p).
Proof.
intros n m p.
induction n as [| nn].
simpl.
reflexivity.
simpl.
rewrite -> IHnn.
reflexivity.
Qed.

Theorem plus_0_r : forall n : nat,
  n + 0 = n.
Proof. 
induction n as [|nn].
reflexivity.
simpl. rewrite -> IHnn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m: nat,
  S (n + m) = n + (S m).
Proof.
intros n m.
induction n as [| nn].
simpl. reflexivity.
simpl. rewrite -> IHnn. reflexivity.
Qed.

Theorem plus_comm : forall a b : nat,
  a + b = b + a.
Proof.
intros a b.
induction a as [|aa].
simpl. rewrite -> plus_0_r. reflexivity.
simpl. rewrite -> IHaa.
rewrite -> plus_n_Sm. reflexivity.
Qed. 

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
intros n m p.
rewrite <- assoc_add.
rewrite <- assoc_add.
assert(H1 : m + n = n + m). rewrite <- plus_comm. reflexivity.
rewrite <- H1. reflexivity.
Qed. 

(* Now prove commutativity of multiplication. (You will probably need to 
define and prove a separate subsidiary theorem to be used in the proof of 
this one.) You may find that plus_swap comes in handy. *)

Fixpoint mult (n : nat) (m :nat) : nat :=
match n with 
| O => O
| S(O) => m
| S(nn) => plus m (mult nn m)
end.

(* COMMUTATIVITY OF MULT *)
Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  intros m n.
  induction n as [| nn].
  Theorem mult_0_r : forall n : nat,
    n * 0 = 0.
    Proof.
      intros n.
      induction n as [|nn].
      simpl. reflexivity.
      simpl. rewrite -> IHnn. reflexivity. 
    Qed.
  simpl. rewrite -> mult_0_r. reflexivity. 
  simpl. rewrite <- IHnn.
  Theorem mult_m_Sn : forall n m,
    m * S n = m * n + m.
    Proof.
      intros foo bar.
      induction bar as [| barf].
      simpl. reflexivity. 
      simpl. rewrite -> IHbarf. rewrite <- assoc_add. rewrite <- plus_n_Sm. reflexivity.
    Qed.
  Theorem add_comm_mult : forall n m p,
    n + m * p = m * p + n.
  Proof.
    intros n m p.
    induction n as [| nn].
    simpl. rewrite -> plus_0_r. reflexivity. 
    simpl. rewrite -> IHnn. rewrite -> plus_n_Sm. reflexivity. 
  Qed.  
  rewrite -> mult_m_Sn. rewrite -> add_comm_mult. reflexivity. 
Qed.

(* Exercise: 2 stars, optional (evenb_n__oddb_Sn) *)
Theorem evenb_n__oddb_Sn :  forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intros n.
  induction n as [|nn].
  simpl. reflexivity.   
  Theorem times_two : forall b : nat,
    evenb b = evenb (S (S b)).
  Proof. intros b. simpl. reflexivity. Qed. 
  rewrite <- times_two. rewrite -> IHnn.   
  Theorem neg_idem : forall b : bool,
    b = negb (negb b).
  Proof. 
    intros b. destruct b. 
    simpl. reflexivity. 
    simpl. reflexivity. 
  Qed. 
  rewrite <- neg_idem. reflexivity.
Qed. 

(* Exercise: 3 stars, optional (more_exercises)
Take a piece of paper. For each of the following theorems, first think 
about whether (a) it can be proved using only simplification and rewriting, 
(b) it also requires case analysis (destruct), or (c) it also requires 
induction. Write down your prediction. Then fill in the proof. (There is no
 need to turn in your piece of paper; this is just to encourage you to 
reflect before hacking!) *)

Fixpoint ble_nat (n : nat) (m : nat) : bool :=
  match (n, m) with
  | (O, O) => true
  | (O, S(mm)) => true
  | (S(nn), O) => false
  | (S(nn), S(mm)) => ble_nat nn mm
  end.

Theorem ble_nat_refl : forall n:nat,
  true = ble_nat n n.
Proof.
  intros n. induction n as [|nn]. 
  simpl. reflexivity.
  simpl. rewrite <- IHnn. reflexivity. 
Qed.

Fixpoint beq_nat (n : nat) (m : nat) : bool :=
match (n, m) with
| (O, O) => true
| (O, S(q)) | (S(q), O) => false
| (S(nn), S(mm)) => beq_nat nn mm
end.

Theorem zero_nbeq_S :  forall n:nat,
  beq_nat 0 (S n) = false.
Proof. intros n. simpl. reflexivity. Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b. destruct b.
  simpl. reflexivity. 
  simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l :  forall n m p : nat,
  ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p. induction p as [| pp].
  simpl. induction n as [| nn]. 
  Theorem zero_ble_S : forall n : nat,
    ble_nat 0 n = true.
  Proof.
    intros n. induction n as [| nn]. 
    simpl. reflexivity. 
    simpl. reflexivity. 
  Qed. 
  rewrite -> zero_ble_S. reflexivity.
  destruct (ble_nat (S nn) m). reflexivity. 
  intro H. rewrite <- H. reflexivity. 
  simpl. intro H. rewrite <- IHpp. 
  reflexivity. rewrite -> H. reflexivity. 
Qed. 

Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof. intros n. simpl. reflexivity. Qed.

Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof. intros n. simpl. rewrite -> plus_0_r. reflexivity. Qed.

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
 rewrite <- plus_comm. rewrite -> assoc_add.
 reflexivity. 
Qed. 

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
 intros n m p. induction n as [| nn]. 
 simpl. reflexivity.
 simpl. rewrite -> mult_plus_distr_r. rewrite -> IHnn. reflexivity. 
Qed. 

(* Exercise: 2 stars, optional (plus_swap')
The replace tactic allows you to specify a particular subterm to rewrite and what you 
want it rewritten to. More precisely, replace (t) with (u) replaces (all copies of) 
expression t in the goal by expression u, and generates t = u as an additional subgoal. 
This is often useful when a plain rewrite acts on the wrong part of the goal.
Use the replace tactic to do a proof of plus_swap', just like plus_swap but without 
needing assert (n + m = m + n). *)

Theorem plus_swap' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
 intros n m p. rewrite <- plus_comm. replace (n + p) with (p + n). rewrite <- assoc_add. reflexivity. 
 rewrite -> plus_comm. reflexivity. 
Qed. 

(* Exercise: 3 stars, optional *)
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
Theorem bool_fn_applied_thrice :
 forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof. 
 intros f b. 
 destruct b. 
 Case "b = true".
 remember (f true) as ftrue.
  destruct ftrue. 
  SCase "f true = true".
   rewrite <- Heqftrue. 
   symmetry. 
   apply Heqftrue.
  SCase "f true = false".
   remember (f false) as ffalse.
   destruct ffalse. 
   SSCase "f false = true". 
    symmetry. 
    apply Heqftrue. 
   SSCase "f false = false".
    symmetry. 
    apply Heqffalse. 
 remember (f false) as ffalse. 
  destruct ffalse. 
  SCase "f false = true".
   remember (f true) as ftrue. 
   destruct ftrue.
    SSCase "f true = true".
     symmetry. 
     apply Heqftrue. 
    SSCase "f true = false". 
     symmetry. 
     apply Heqffalse.
  SCase "f false = false".
   rewrite <- Heqffalse. 
   symmetry. 
   apply Heqffalse. 
Qed.

(* Exercise: 4 stars, recommended (binary)
Consider a different, more efficient representation of natural numbers using a binary 
rather than unary system. That is, instead of saying that each natural number is either 
zero or the successor of a natural number, we can say that each binary number is either

    zero,
    twice a binary number, or
    one more than twice a binary number.

(a) First, write an inductive definition of the type bin corresponding to this 
description of binary numbers.
(Hint: recall that the definition of nat from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat → nat.
says nothing about what O and S "mean". It just says "O is a nat (whatever that is), 
and if n is a nat then so is S n". The interpretation of O as zero and S as 
successor/plus one comes from the way that we use nat values, by writing functions to 
do things with them, proving things about them, and so on. Your definition of bin should 
be correspondingly simple; it is the functions you will write next that will give it 
mathematical meaning.) *)

Inductive bin : Type :=
| inf : bin
| zero : bin -> bin
| one : bin -> bin.

(* (b) Next, write an increment function for binary numbers, and a function to convert 
binary numbers to unary numbers. *)

(* inf
   zero inf : 0
   one inf : 1
   one (zero inf) : 2
   one (one inf) : 3
one (one inf) -> one (inc (one inf)) -> one (one (inc inf)) -> one (one (zero inf)) 
odd (odd O) -> even
   one (zero (zero inf)) : 4
*)

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


(* Exercise: 2 stars, optional (decreasing) 
The requirement that some argument to each function be "decreasing" is a 
fundamental feature of Coq's design: In particular, it guarantees that every 
function that can be defined in Coq will terminate on all inputs. However, 
because Coq's "decreasing analysis" is not very sophisticated, it is 
sometimes necessary to write functions in slightly unnatural ways.
To get a concrete sense of this, find a way to write a sensible Fixpoint 
definition (of a simple function on numbers, say) that does terminate on 
all inputs, but that Coq will not accept because of this restriction. *)

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
