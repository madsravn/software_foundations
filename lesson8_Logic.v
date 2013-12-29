Require Export case.
Require String.
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
  intros n.
  induction n as [|nn].
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
Inductive True : Prop :=
| triv : True.

(*** Check this constructor ***)
Theorem check_true : forall A, A -> True.
Proof.
  intros A H.
  apply triv.
 Qed.

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

(***
Theorem double_neg_imp : forall P : Prop,
                           ~~ P -> P.
Proof. 
  unfold not.
  intros P H.
  (no evidence to say anything else)
***)

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
Theorem ex_falso_quot_liblet : forall P : Prop, 
                                 False -> P.
Proof. intros P H. inversion H. Qed.


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

Theorem classic_peirce : classic <-> peirce.
Proof. 
  split. unfold classic. unfold peirce.
  intros classic P Q.
  intro H1. apply classic.
  unfold not. intro notP. apply notP. apply H1.
  intro H2. apply classic. unfold not.
  intro notQ. apply notP in H2.
  apply H2.
  unfold classic. unfold peirce.
  intros peirce P notnotP.
  unfold not in notnotP.
  apply peirce with (P:=P) (Q:=False).
  intro H1.
  apply ex_falso_quot_liblet.
  apply notnotP.
  apply H1.
Qed.  

Theorem excluded_middle_implies_to_or : implies_to_or <-> excluded_middle.
Proof.
  split. unfold excluded_middle. unfold implies_to_or.
  intros ex_mid.
(*  apply or_introl with (A:=Q->R) (B:=(Q->R) -> False) in H1. *)
Admitted.  
  
  


Theorem imples_to_or_de_morgan_not_and_not : implies_to_or <-> de_morgan_not_and_not.
Proof.
  split. unfold implies_to_or. unfold de_morgan_not_and_not.
  intros implies_to_or P Q H1.
Admitted.  

(* Theorem peirce_excluded_middle : peirce <-> excluded_middle. *)
(* Proof.  *)
(*   split. unfold peirce. unfold excluded_middle. *)
(*   intros peirce P. *)
(*   left. *)
(*   apply peirce with (P:=P) (Q:=False). *)
(*   intro notP. *)
(*   apply ex_falso_quot_liblet. *)
(*   generalize notP. *)
  
(*   apply peirce with (P:=False) (Q:=P). *)
(*   intro H. *)


(* Theorem classic_excluded_middle : classic <-> excluded_middle. *)
(* Proof.  *)
(*   split. unfold classic. unfold excluded_middle. *)
(*   intros classic P. *)
(*   left.  *)
(*   apply classic. *)
(*   intro notP. *)
(*   apply notP. *)
  


(**************************************************
 Exercise: 2 stars (false_beq_nat)
**************************************************)
Fixpoint beq_nat n m :=
  match (n, m) with
    | (O, O) => true
    | (O, _) | (_, O) => false
    | (S nn, S mm) => beq_nat nn mm
  end.


Theorem false_beq_nat : forall n m : nat,
                          n <> m ->
                          beq_nat n m = false.
Proof.
  intros n m H.
  unfold not in H.
  generalize dependent n.
  induction m as [|mm].
  intros n H.
  destruct n. 
  simpl. apply ex_falso_quot_liblet. apply H. reflexivity.
  simpl. reflexivity.
  intros n. destruct n as [|nn].
  intros H. simpl. reflexivity.
  simpl. intro H. apply IHmm. intro E. 
  apply H. SearchAbout S.
  apply eq_S. apply E.
Qed.



(**************************************************
Exercise: 2 stars, optional (beq_nat_false)
**************************************************)
Theorem beq_nat_false :  forall n m,
                           beq_nat n m = false -> n <> m.
Proof.
  intros n.
  unfold not.
  induction n as [|nn].
  destruct m as [|mm].
  simpl. intro H. inversion H.
  simpl. intro H1. intro H2. inversion H2.
  destruct m as [|mm].
  simpl. intros H1 H2. inversion H2.
  simpl. intros H1 H2. apply eq_add_S in H2.
  generalize H2. generalize H1. apply IHnn.
Qed.
 


(**************************************************
Exercise: 2 stars, optional (ble_nat_false)
**************************************************)
Fixpoint ble_nat (n:nat) (m:nat) := match (n, m) with 
                                      | (O, _) => true
                                      | (S _, O) => false
                                      | (S nn, S mm) => ble_nat nn mm
                                    end.

Theorem ble_nat_false : forall n m,
                          ble_nat n m = false -> ~(n <= m).
Proof.
  intros n. induction n as [|nn].
  intros m H E.
  destruct m as [|mm].
  simpl in H. inversion H.
  simpl in H. inversion H.
  intros m E. destruct m as [|mm].
  unfold not. intro EE. inversion EE.
  simpl in E. unfold not. intro EE.
  simpl in EE. apply Le.le_S_n in EE.
  generalize dependent EE.
  generalize dependent E.
  apply IHnn.
Qed.



(**************************************************
Exercise: 1 star (dist_not_exists)
Prove that "P holds for all x" implies "there is no x for which P does not hold."
**************************************************)
Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
                            (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H1 H2.
  inversion H2.
  unfold not in H.
  apply H.
  apply H1.
Qed.



(**************************************************
Exercise: 3 stars, optional (not_exists_dist)
(The other direction of this theorem requires the classical "law of the excluded middle".)
**************************************************)
Theorem not_exists_dist : excluded_middle ->
                          forall (X:Type) (P : X -> Prop),
                            ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros ex_mid X P. 
  unfold excluded_middle in ex_mid. unfold not.
  intros H1 x0.
  Admitted.
  
  

(**************************************************
Exercise: 2 stars (dist_exists_or)
Prove that existential quantification distributes over disjunction.
**************************************************)
Theorem dist_exists_or : forall (X:Type) 
                                (P Q : X -> Prop),
                           (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  intros H1. inversion H1.
  inversion H as [HL|HR].
  left. exists x. apply HL.
  right. exists x. apply HR.
  intros H. inversion H as [HL|HR].
  inversion HL.
  exists x.
  left. apply H0.
  inversion HR.
  exists x.
  right.
  apply H0.
Qed.




(**************************************************
Exercise: 2 stars (leibniz_equality)
The inductive definitions of equality corresponds to Leibniz equality: what we mean when we say "x and y are equal" is that every property on P that is true of x is also true of y.
**************************************************)
Lemma leibniz_equality : forall (X : Type) (x y: X), 
                           x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros X x y H P E.
  rewrite -> H in E.
  apply E.
Qed.



(**************************************************
Exercise: 1 star (override_shadow')
**************************************************)
Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|nn].
  destruct m as [|mm].
  left. reflexivity.
  right. intros H. inversion H.
  intros m. destruct m as [|mm].
  right. intros H. inversion H.
  destruct IHnn with (m:=mm) as [eq|neq].
  left. apply f_equal. apply eq.
  right. intros H. inversion H. generalize H1. apply neq.
Qed.

Definition override' {X: Type} (f: nat -> X) (k:nat) (x:X) : nat -> X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat -> X),
                             (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override'. destruct (eq_nat_dec k1 k2) as [E1|E2].
  reflexivity. reflexivity.
Qed.



(**************************************************
Exercise: 1 star, optional (dist_and_or_eq_implies_and)
**************************************************)
Lemma dist_and_or_eq_implies_and : forall P Q R,
                                     P /\ (Q \/ R) /\ Q = R -> P\/ Q.
Proof.
  intros P Q R H.
  inversion H.
  left. apply H0.
Qed.


(**************************************************
Exercise: 3 stars (all_forallb)
Inductively define a property all of lists, parameterized by a type X and a property P : X → Prop, such that all X P l asserts that P is true for every element of the list l.
**************************************************)

Definition empty {X:Type} (l:list X) : Prop :=
  match l with
    | nil => True
    | _ => False
  end.

Definition tail {X:Type} (l:list X) : list X :=
  match l with
    | nil => nil
    | cons _ tl => tl
  end.

Definition head {X:Type} (l:list X) (default:X) :  X :=
  match l with
    | nil => default
    | cons hd _ => hd
  end.

(* Inductive all (X : Type) (P : X -> Prop) : list X -> Prop := *)
(* | all_elts : *)
(*     forall l : list X, *)
(*       match l with *)
(*         | nil => all X P nil -> True *)
(*         | cons hd tl => P hd /\ all X P tl *)
(*       end. *)
    
(*   | b : forall l : list X, (empty l) -> all X P nil *)
(*   | a : forall l, P (hd l ) -> all X P (tail l). *)


(** Recall the function forallb, from the exercise forall_exists_challenge in chapter Poly: **)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | nil => true
    | cons x l' => andb (test x) (forallb test l')
  end.

(* Using the property all, write down a specification for forallb, and prove that it satisfies the specification. Try to make your specification as precise as possible.
Are there any important properties of the function forallb which are not captured by your specification? *)

(* FILL IN HERE *)

(**************************************************
Exercise: 4 stars, advanced (filter_challenge)
One of the main purposes of Coq is to prove that programs match their specifications. To this end, let's prove that our definition of filter matches a specification. Here is the specification, written out informally in English.
Suppose we have a set X, a function test: X→bool, and a list l of type list X. Suppose further that l is an "in-order merge" of two lists, l1 and l2, such that every item in l1 satisfies test and no item in l2 satisfies test. Then filter test l = l1.
A list l is an "in-order merge" of l1 and l2 if it contains all the same elements as l1 and l2, in the same order as l1 and l2, but possibly interleaved. For example,
    [1,4,6,2,3]
is an in-order merge of
    [1,6,2]
and
    [4,3].
Your job is to translate this specification into a Coq theorem and prove it. (Hint: You'll need to begin by defining what it means for one list to be a merge of two others. Do this with an inductive relation, not a Fixpoint.)
**************************************************)


(**************************************************
Exercise: 5 stars, advanced, optional (filter_challenge_2)
A different way to formally characterize the behavior of filter goes like this: Among all subsequences of l with the property that test evaluates to true on all their members, filter test l is the longest. Express this claim formally and prove it.
**************************************************)


(**************************************************
Exercise: 4 stars, advanced (no_repeats)
The following inductively defined proposition...
**************************************************)
Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(* ...gives us a precise way of saying that a value a appears at least once as a member of a list l.
Here's a pair of warm-ups about appears_in. *)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs ∨ appears_in x ys.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs ∨ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  (* FILL IN HERE *) Admitted.

(* Now use appears_in to define a proposition disjoint X l1 l2, which should be provable exactly when l1 and l2 are lists (with elements of type X) that have no elements in common. *)

(* FILL IN HERE *)

(* Next, use appears_in to define an inductive proposition no_repeats X l, which should be provable exactly when l is a list (with elements of type X) where every member is different from every other. For example, no_repeats nat [1,2,3,4] and no_repeats bool [] should be provable, while no_repeats nat [1,2,1] and no_repeats bool [true,true] should not be. *)

(* FILL IN HERE *)

(* Finally, state and prove one or more interesting theorems relating disjoint, no_repeats and ++ (list append). *)

(* FILL IN HERE *)

(**************************************************
Exercise: 3 stars (nostutter)
Formulating inductive definitions of predicates is an important skill you'll need in this course. Try to solve this exercise without any help at all (except from your study group partner, if you have one).
We say that a list of numbers "stutters" if it repeats the same number consecutively. The predicate "nostutter mylist" means that mylist does not stutter. Formulate an inductive definition for nostutter. (This is different from the no_repeats predicate in the exercise above; the sequence 1,4,1 repeats but does not stutter.)
**************************************************)
Inductive nostutter: list nat -> Prop :=
 (* FILL IN HERE *)
.

(* Make sure each of these tests succeeds, but you are free to change the proof if the given one doesn't work for you. Your definition might be different from mine and still correct, in which case the examples might need a different proof.
The suggested proofs for the examples (in comments) use a number of tactics we haven't talked about, to try to make them robust with respect to different possible ways of defining nostutter. You should be able to just uncomment and use them as-is, but if you prefer you can also prove each example with more basic tactics. *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2: nostutter [].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3: nostutter [5].
(* FILL IN HERE *) Admitted.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4: not (nostutter [3;1;1;4]).
(* FILL IN HERE *) Admitted.
(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)

(**************************************************
Exercise: 4 stars, advanced (pigeonhole principle)
The "pigeonhole principle" states a basic fact about counting: if you distribute more than n items into n pigeonholes, some pigeonhole must contain at least two items. As is often the case, this apparently trivial fact about numbers requires non-trivial machinery to prove, but we now have enough...
First a pair of useful lemmas (we already proved these for lists of naturals, but not for arbitrary lists).
**************************************************)
Lemma app_length : ∀(X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma appears_in_app_split : ∀(X:Type) (x:X) (l:list X),
  appears_in x l → 
  ∃l1, ∃l2, l = l1 ++ (x::l2).
Proof.
  (* FILL IN HERE *) Admitted.

(* Now define a predicate repeats (analogous to no_repeats in the exercise above), such that repeats X l asserts that l contains at least one repeated element (of type X). *)

Inductive repeats {X:Type} : list X → Prop :=
  (* FILL IN HERE *)
.

(* Now here's a way to formalize the pigeonhole principle. List l2 represents a list of pigeonhole labels, and list l1 represents an assignment of items to labels: if there are more items than labels, at least two items must have the same label. You will almost certainly need to use the excluded_middle hypothesis. *)

Theorem pigeonhole_principle: ∀(X:Type) (l1 l2:list X),
  excluded_middle → 
  (∀x, appears_in x l1 → appears_in x l2) → 
  length l2 < length l1 → 
  repeats l1.
Proof. intros X l1. induction l1.
  (* FILL IN HERE *) Admitted.
