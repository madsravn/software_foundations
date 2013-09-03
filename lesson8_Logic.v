(* Software Foundations Chapter 8 : Logic in Coq *)


(**************************************************
 Exercise: 1 star, optional (proj2)
**************************************************)
Theorem proj2 : forall P Q : Prop,
                  P /\ Q -> Q.
Proof.
  intros P Q E.
  inversion E as [p q].
  apply q.
Qed.



(**************************************************
Exercise: 2 stars (and_assoc)
In the following proof, notice how the nested pattern in the inversion breaks the hypothesis H : P ∧ (Q ∧ R) down into HP: P, HQ : Q, and HR : R. Finish the proof from there:
**************************************************)
Theorem and_assoc : forall P Q R : Prop,
                      P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split. split. apply HP. apply HQ. apply HR.
Qed.



(**************************************************
Exercise: 2 stars (even__ev)
Now we can prove the other direction of the equivalence of even and ev, which we left hanging in chapter Prop. Notice that the left-hand conjunct here is the statement we are actually interested in; the right-hand conjunct is needed in order to make the induction hypothesis strong enough that we can carry out the reasoning in the inductive step. (To see why this is needed, try proving the left conjunct by itself and observe where things get stuck.)
**************************************************)
Inductive ev : nat -> Prop :=
  ev_0 : ev 0
| ev_SS : forall n, ev n -> ev (S (S n)).

Fixpoint evenb n : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n) => evenb n
  end.

Definition even n : Prop := evenb n = true.

Theorem even__ev : forall n : nat,
                     (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros n. induction n as [|nn].
  split.
  intro H. apply ev_0.
  intro H. inversion H.
  inversion IHnn as [E1 E2].
  split.
  apply E2.
  intro H.
  unfold even in H. simpl in H.
  apply ev_SS.
  generalize H.
  unfold even in E1.
  apply E1.
Qed.



(**************************************************
  Exercise: 1 star, optional (iff_properties)
  Using the above proof that ↔ is symmetric (iff_sym) as a guide, prove that it is also reflexive and transitive.
**************************************************)
Theorem iff_refl : forall P : Prop,
                     P <-> P.
Proof.
  intros P. split.
  intro H. apply H.
  intro H. apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop,
                      (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR.
  inversion HPQ as [HP2Q HQ2P]. inversion HQR as [HQ2R HR2Q].
  split.
  intro HP. 
  apply HQ2R in HP2Q. apply HP2Q. apply HP.
  intro HR.
  apply HQ2P in HR2Q. apply HR2Q. apply HR.
Qed.



(**************************************************
  Exercise: 2 stars (or_distributes_over_and_2)
 **************************************************)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
                                      (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H as [[HP1 | HQ ] [HP2 | HR]].
  left. apply HP1. left. apply HP1. left. apply HP2.
  right. split. apply HQ. apply HR.
Qed.



(**************************************************
 Exercise: 1 star, optional (or_distributes_over_and)
 **************************************************)
Theorem or_distributes_over_and : forall P Q R : Prop,
                                    P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  intro H. split.
  inversion H as [HP | [HQ  HR]].
  left. apply HP. right. apply HQ.
  inversion H as [HP | [HQ HR]].
  left. apply HP. right. apply HR.
  intro H. 
  inversion H as [[HP1 | HQ] [HP2 | HR]].
  left. apply HP1. left. apply HP1. left. apply HP2.
  right. split. apply HQ. apply HR.
Qed.



(**************************************************
 Exercise: 2 stars, optional (bool_prop)
 **************************************************)
Theorem andb_false : forall b c,
                       andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b. destruct c.
  simpl in H. left. apply H.
  simpl in H. right. apply H.
  destruct c.
  simpl in H. left. apply H.
  simpl in H. left. apply H.
Qed.

Theorem orb_prop : forall b c,
                     orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b. destruct c.
  simpl in H. left. apply H.
  simpl in H. left. apply H.
  destruct c.
  simpl in H. right. apply H.
  simpl in H. right. apply H.
Qed.

Theorem orb_false_elim : forall b c,
                           orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  split.
  destruct b. simpl in H. apply H.
  destruct c. simpl in H. inversion H.
  apply H.
  destruct b. inversion H.
  simpl in H. apply H.
Qed.

(**************************************************
 Exercise: 2 stars, advanced (True)
 Define True as another inductively defined proposition. (The intution is that True should be a proposition for which it is trivial to give evidence.)
 **************************************************)
Inductive True : Prop -> Prop :=
| triv : forall P : Prop, True P.



(**************************************************
 Exercise: 2 stars, advanced (double_neg_inf)
 Write an informal proof of double_neg:
 **************************************************)
Theorem double_neg_inf : forall P : Prop,
                           P -> ~~P.
Proof. 
  intros P H1.
  unfold not. intro H2.
  apply H2 in H1.
  inversion H1.
Qed.
(** 
Theorem: P implies ~~P, for any proposition P.
Proof: Let P be some proposition. First consider ~P. This is equivalent to the statement that
the proposition P implies the proposition False. Now consider ~~P. This states the if ~P holds, then we can 
derive False. Therefore, the statement we are really trying to prove is P -> (P -> False) -> False. Assume P and P -> False. From these two assumptions we can derive False and use this evidence to complete the proof. 
**)



(**************************************************
  Exercise: 2 stars (contrapositive)
 **************************************************)

Theorem contrapositive : forall P Q : Prop,
                           (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q E1.
  unfold not.
  intros E2 E3.
  apply E1 in E3.
  apply E2 in E3.
  apply E3.
Qed.  



(**************************************************
 Exercise: 1 star (not_both_true_and_false)
 **************************************************)
Theorem not_both_true_and_false : forall P : Prop,
                                    ~ (P /\ ~P).
Proof.
  intros P. unfold not.
  intros H.
  inversion H as [P' P'False].
  apply P'False in P'.
  apply P'.
Qed.



(**************************************************
 Exercise: 1 star, advanced (informal_not_PNP)
 Write an informal proof (in English) of the proposition ∀ P : Prop, ~(P ∧ ~P).
**************************************************)
(** Proof:
 Let ~(P /\ ~P) be represented instead as P /\ (P -> False) -> False. Assume the premises: P /\ (P -> False). Using the left side of the conjunction (P) as evidence for the right (P -> False), we derive False. Use this derivation as evidence for the goal. 
**)



(**************************************************
 Exercise: 1 star (ev_not_ev_S)

 Theorem five_not_even confirms the unsurprising fact that five is not an even number. Prove this more interesting fact:
 **************************************************)
Theorem ev_not_ev_S : forall n,
                        ev n -> ~ ev (S n).
Proof.
  unfold not. intros n H. induction H. (* not n! *)
  intro E. inversion E.
  intro E. inversion E as [|nn HevS1 Hnh].
  apply IHev in HevS1. inversion HevS1.
Qed.

(**
Note that some theorems that are true in classical logic are not provable in Coq's (constructive) logic. E.g., let's look at how this proof gets stuck...
**)

Theorem classic_double_neg : forall P : Prop,
                               ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H.
  (* But now what? There is no way to "invent" evidence for ~P 
     from evidence for P. *)
  Abort.



(***************************************************
 Exercise: 5 stars, advanced, optional (classical_axioms)

 For those who like a challenge, here is an exercise taken from the Coq'Art book (p. 123). The following five statements are often considered as characterizations of classical logic (as opposed to constructive logic, which is what is "built in" to Coq). We can't prove them in Coq, but we can consistently add any one of them as an unproven axiom if we wish to work in classical logic. Prove that these five propositions are equivalent.
**************************************************)
Definition peirce := forall P Q: Prop,
                       ((P -> Q) -> P) -> P.
Definition classic := forall P:Prop,
                        ~~P -> P.
Definition excluded_middle := forall P:Prop,
                                P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop,
                                      ~(~P /\ ~Q) -> P \/ Q.
Definition implies_to_or := forall P Q : Prop,
                              (P -> Q) -> (~P \/ Q).

Theorem classic_excluded_middle : forall P,
                                    (~~P -> P) <-> (P \/ ~P).
Proof. 
  intros P. split.
  intros H.
Admitted.


(**************************************************
 Exercise: 2 stars (false_beq_nat)
**************************************************)
Fixpoint beq_nat n m :=
  match (n, m) with
    | (O, O) => true
    | (O, _) | (_, O) => false
    | (S nn, S mm) => beq_nat nn mm
  end.

Theorem ex_falso_quot_liblet : forall P : Prop, 
                                 False -> P.
Proof. intros P H. inversion H. Qed.

Theorem false_beq_nat : forall n m : nat,
                          n <> m ->
                          beq_nat n m = false.
Proof.
  intros n m H.
  destruct n as [|nn]. destruct m as [|mm].
  simpl. unfold not in H.
  assert (Lem1 : 0 = 0). reflexivity.
  apply H in Lem1.
  apply ex_falso_quot_liblet.
  apply Lem1.
  simpl. unfold not in H.

Exercise: 2 stars, optional (beq_nat_false)
Theorem beq_nat_false : ∀n m,
  beq_nat n m = false → n <> m.
Proof.
  (* FILL IN HERE *) Admitted.
☐
Exercise: 2 stars, optional (ble_nat_false)
Theorem ble_nat_false : ∀n m,
  ble_nat n m = false → ~(n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
☐

**************************************************
**************************************************