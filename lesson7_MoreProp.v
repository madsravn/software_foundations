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

Theorem plus_lt : forall n1 n2 m,
                    n1 + n2 < m ->
                    n1 < m /\ n2 < m.
Proof.
  unfold lt.
  intros n1 n2 m E1.
  induction E1.
  
    

Theorem lt_S : ∀n m,
  n < m →
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : ∀n m,
  ble_nat n m = true → n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : ∀n m,
  n <= m →
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on m. *)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : ∀n m o,
  ble_nat n m = true → ble_nat m o = true → ble_nat n o = true.
Proof.
  (* Hint: This theorem can be easily proved without using induction. *)
  (* FILL IN HERE *) Admitted.

Exercise: 3 stars (R_provability)
Module R.
We can define three-place relations, four-place relations, etc., in just the same way as binary relations. For example, consider the following three-place relation on numbers:

Inductive R : nat → nat → nat → Prop :=
   | c1 : R 0 0 0 
   | c2 : ∀m n o, R m n o → R (S m) n (S o)
   | c3 : ∀m n o, R m n o → R m (S n) (S o)
   | c4 : ∀m n o, R (S m) (S n) (S (S o)) → R m n o
   | c5 : ∀m n o, R m n o → R n m o.

Which of the following propositions are provable?
R 1 1 2
R 2 2 6
If we dropped constructor c5 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.
If we dropped constructor c4 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.
(* FILL IN HERE *)
☐
Exercise: 3 stars, optional (R_fact)
Relation R actually encodes a familiar function. State and prove two theorems that formally connects the relation and the function. That is, if R m n o is true, what can we say about m, n, and o, and vice versa?

(* FILL IN HERE *)
☐

End R.


Exercise: 2 stars (total_relation)
Define an inductive binary relation total_relation that holds between every pair of natural numbers.

(* FILL IN HERE *)
☐
Exercise: 2 stars (empty_relation)
Define an inductive binary relation empty_relation (on numbers) that never holds.

(* FILL IN HERE *)
☐
Exercise: 2 stars, optional (le_exercises)
Here are a number of facts about the <= and < relations that we are going to need later in the course. The proofs make good practice exercises.

Lemma le_trans : ∀m n o, m <= n → n <= o → m <= o.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem O_le_n : ∀n,
  0 <= n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem n_le_m__Sn_le_Sm : ∀n m,
  n <= m → S n <= S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem Sn_le_Sm__n_le_m : ∀n m,
  S n <= S m → n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_plus_l : ∀a b,
  a <= a + b.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_lt : ∀n1 n2 m,
  n1 + n2 < m →
  n1 < m ∧ n2 < m.
Proof.
 unfold lt.
 (* FILL IN HERE *) Admitted.

Theorem lt_S : ∀n m,
  n < m →
  n < S m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true : ∀n m,
  ble_nat n m = true → n <= m.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem le_ble_nat : ∀n m,
  n <= m →
  ble_nat n m = true.
Proof.
  (* Hint: This may be easiest to prove by induction on m. *)
  (* FILL IN HERE *) Admitted.

Theorem ble_nat_true_trans : ∀n m o,
  ble_nat n m = true → ble_nat m o = true → ble_nat n o = true.
Proof.
  (* Hint: This theorem can be easily proved without using induction. *)
  (* FILL IN HERE *) Admitted.

Exercise: 3 stars (R_provability)
Module R.
We can define three-place relations, four-place relations, etc., in just the same way as binary relations. For example, consider the following three-place relation on numbers:

Inductive R : nat → nat → nat → Prop :=
   | c1 : R 0 0 0 
   | c2 : ∀m n o, R m n o → R (S m) n (S o)
   | c3 : ∀m n o, R m n o → R m (S n) (S o)
   | c4 : ∀m n o, R (S m) (S n) (S (S o)) → R m n o
   | c5 : ∀m n o, R m n o → R n m o.

Which of the following propositions are provable?
R 1 1 2
R 2 2 6
If we dropped constructor c5 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.
If we dropped constructor c4 from the definition of R, would the set of provable propositions change? Briefly (1 sentence) explain your answer.
(* FILL IN HERE *)
☐
Exercise: 3 stars, optional (R_fact)
Relation R actually encodes a familiar function. State and prove two theorems that formally connects the relation and the function. That is, if R m n o is true, what can we say about m, n, and o, and vice versa?

(* FILL IN HERE *)
☐

End R. 