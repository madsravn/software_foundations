(* Software Foundadations Chapter 7 : More about Propositions and Evidence *)

(**************************************************
  Exercise: 2 stars (total_relation)
  Define an inductive binary relation total_relation that holds between every pair of natural numbers.
 **************************************************)
Inductive total_relation : nat -> nat -> Prop :=
| tr : forall n m : nat, total_relation n m.



(**************************************************
 Exercise: 2 stars (empty_relation)
 Define an inductive binary relation empty_relation (on numbers) that never holds.
 **************************************************)
Inductive empty_relation : nat -> nat -> Prop :=
| er : forall n m : nat, 2 + 2 = 5 -> empty_relation n m.



(**************************************************
  Exercise: 2 stars, optional (le_exercises)
  Here are a number of facts about the <= and < relations that we are going to need later in the course. The proofs make good practice exercises.
 **************************************************)
Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o E1.
  inversion E1 as [H1|a H1].
  intro E2.
  apply E2.
  intro E2.
  induction E2 as [H2|b H2].
  generalize H1.  
  apply le_S.
  generalize IHH2.
  apply le_S.
Qed.

Theorem O_le_n : forall n,
                   0 <= n.
Proof.
  intros n.
  induction n as [|nn].
  apply le_n.
  generalize IHnn.
  apply le_S.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
                             n <= m -> S n <= S m.
Proof.
  intros n m E.
  induction E.
  apply le_n.
  apply le_S.
  apply IHE.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
                             S n <= S m -> n <= m.
Proof.
  intros n m E.
  inversion E as [H|a H1 H2].
  apply le_n.
  generalize H1.
  apply le_trans.
  apply le_S.
  apply le_n.
Qed.

Theorem le_plus_l : forall a b,
                      a <= a + b.
Proof.
  intros a b.
  induction a as [|aa].
  simpl.
  apply O_le_n.
  rewrite plus_Sn_m.
  apply n_le_m__Sn_le_Sm.
  apply IHaa.
Qed.

Theorem plus_comm : forall m n,
                      m + n = n + m.
Proof. 
  intros m n. induction n as [|nn]. 
  simpl. rewrite plus_n_O. reflexivity.
  rewrite <- plus_n_Sm. rewrite IHnn. rewrite <- plus_Sn_m. reflexivity.
Qed.

Theorem plus_lt : forall n1 n2 m,
                    n1 + n2 < m ->
                    n1 < m /\ n2 < m.
Proof.
  unfold lt. 
  split.  
  generalize H.
  apply le_trans.
  rewrite <- plus_Sn_m. 
  apply le_plus_l.
  generalize H.
  apply le_trans.
  rewrite plus_n_Sm. 
  rewrite plus_comm.
  apply le_plus_l.
Qed.

Theorem lt_S : forall n m,
                 n < m ->  n < S m.
Proof.
  unfold lt.
  intros n m.
  apply le_S.
Qed.

Fixpoint ble_nat n m : bool :=
match (n,m) with
| (O,_) => true
| (_,O) => false
| (S n, S m) => ble_nat n m
end.

Theorem ble_nat_true : forall n m,
                         ble_nat n m = true -> n <= m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|mm].
  intros n H. destruct n.
  apply le_n.
  inversion H.
  intros n H. destruct n.
  apply O_le_n.
  apply n_le_m__Sn_le_Sm.
  simpl in H.
  generalize H.
  apply IHmm.
Qed.

Theorem le_ble_nat : forall n m,
                       n <= m -> ble_nat n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|mm].
  intros n H. inversion H.
  simpl. reflexivity.
  intros n H.
  destruct n as [|nn].
  simpl. reflexivity.
  simpl. apply Sn_le_Sm__n_le_m in H.
  generalize H.
  apply IHmm.
Qed.

Theorem ble_nat_true_trans : forall n m o,
                               ble_nat n m = true ->
                               ble_nat m o = true ->
                               ble_nat n o = true.
Proof.
  intros n m o E1 E2.
  apply ble_nat_true in E1.
  apply ble_nat_true in E2.
  apply le_ble_nat.
  generalize E2. generalize E1.
  apply le_trans.
Qed.



(**************************************************
 Exercise: 3 stars (R_provability)
**************************************************)
Module R.
(**
  We can define three-place relations, four-place relations, etc., in just the same way as binary relations. For example, consider the following three-place relation on numbers:
**)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.


(** Which of the following propositions are provable? **)
Example one : (R 1 1 2).
Proof. apply c2. apply c3. apply c1. Qed.
(** 
Example two : (R 2 2 6).
Proof. apply c2. apply c2. apply c3. apply c3. ...
Not provable.. **)

(** If we dropped constructor c5 from the definition of R, would the set of provable propositions change? **)
(** No **)

(** Briefly (1 sentence) explain your answer. **)
(** c5 gives us no progress; it gives us back what we put in, so we will never choose it as part of proof anyway **)

(** If we dropped constructor c4 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer. **)
(** No; c4 is the inverse of the composition of c2 and c3. Since it does not reduce the answer to c1 and since we can exactly undo its application through c2 and c3, we never use it. *)



(**************************************************
Exercise: 3 stars, optional (R_fact)
Relation R actually encodes a familiar function. State and prove two theorems that formally connects the relation and the function. That is, if R m n o is true, what can we say about m, n, and o, and vice versa?
**************************************************)
Example fact_or_fib_4 : (R 1 2 3).
Proof. 
  apply c2. 
  apply c3. apply c3. 
  apply c1. Qed.
Example fact_or_fib_5 : (R 2 3 5).
Proof. 
  apply c2. apply c2. 
  apply c3. apply c3. apply c3. 
  apply c1. Qed.
Example fact_or_fib_6 : (R 3 5 8).
Proof. 
  apply c2. apply c2. apply c2.
  apply c3. apply c3. apply c3. apply c3. apply c3.
  apply c1. Qed.
(* Clearly this models the fibonnaci sequence, not factorial, as the name would suggest *)

Theorem pred_S : forall m n,
                   S m = S n -> pred (S m) = pred (S n).
Proof. 
  intros m n H.
  destruct  m as [|mm].  destruct n as [|nn].
  reflexivity.
  rewrite H. reflexivity.
  rewrite H. reflexivity.
Qed.

Theorem strip_S : forall m n,
                    S m = S n ->  m = n.
Proof.
  intros n m. generalize dependent n. induction m as [|mm].
  intros n H. destruct n. 
  reflexivity. inversion H.
  intros n H. induction n as [|nn].
  inversion H.
  apply pred_S in H. simpl in H.
  apply pred_S in H. simpl in H.
  rewrite H. reflexivity.
Qed.

Theorem R_is_fib : forall m n o,
                     R m n o -> m + n = o.
Proof. 
  intros m n o H.
  induction H.
  simpl. reflexivity.
  rewrite plus_Sn_m. rewrite IHR. reflexivity.
  rewrite <- plus_n_Sm. rewrite IHR. reflexivity.
  rewrite <- plus_n_Sm in IHR. rewrite plus_Sn_m in IHR.
  apply strip_S in IHR.
  apply strip_S in IHR.
  apply IHR.
  rewrite plus_comm.
  apply IHR.
Qed.

Fixpoint fib i : nat :=
match i with
  | 0 => 0
  | 1 => 1
  | S n => fib n + fib (pred n)
end.

Example fib_ex : (fib 2 = 1).
Proof. simpl. reflexivity. Qed.
Example fib_ex_3 : (fib 3 = 2).
Proof. simpl. reflexivity. Qed.
Example fib_ex_4 : (fib 4 = 3).
Proof. simpl. reflexivity. Qed.
Example fib_ex_5 : (fib 5 = 5).
Proof. simpl. reflexivity. Qed.
Example fib_ex_6 : (fib 6 = 8).
Proof. simpl. reflexivity. Qed.

Theorem fib_is_R : forall x y,
                     x >= 2 -> fib x = y -> R (fib (pred (pred x))) (fib (pred x)) y.
Proof. 
  intros x y E1 E2.
  inversion E1.
  rewrite <- H in E2.
  simpl in E2.
  simpl. rewrite <- E2.
  apply c3. apply c1.
  simpl.
  rewrite <- E2.
  rewrite <- H0.
  simpl.Admitted.


End R.