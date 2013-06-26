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
                       : nat_scope.+ p) = m + (n + p).

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

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
intros n.
induction n as [|nn].
simpl. reflexivity.
simpl. rewrite -> IHnn. reflexivity. 
Qed.

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
intros m n.
induction n as [| nn].
simpl. rewrite -> mult_0_r. reflexivity. 
simpl. rewrite <- IHnn.

Theorem mult_m_Sn : forall n m,
  m * S n = m * n + m.
intros m n.
induction n as [| nn].
simpl. reflexivity. 
simpl. rewrite -> IHnn. rewrite <- assoc_add. rewrite <- plus_n_Sm. reflexivity.
Qed.

Theorem H1 : forall n m p,
  n + m * p = m * p + n.
Proof.
intros n m p.
induction n as [| nn].
simpl. rewrite -> plus_0_r. reflexivity. 
simpl. rewrite -> IHnn. rewrite -> plus_n_Sm. reflexivity. 
Qed.  

rewrite -> mult_m_Sn. rewrite -> H1. reflexivity. 
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
Proof.
intros n. simpl. reflexivity. Qed.

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
   

Theorem S_nbeq_0 : ∀n:nat,
  beq_nat (S n) 0 = false.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_1_l : ∀n:nat, 1 * n = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem all3_spec : ∀b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_plus_distr_r : ∀n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem mult_assoc : ∀n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (* FILL IN HERE *) Admitted.
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

Fixpoint plus3 (n : nat) (m : nat) : nat :=
match n with 
| O => m
| nn => plus3 (pred nn) (S m)
end.
