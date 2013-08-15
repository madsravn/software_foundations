(* Software Foundations Chapter 2 : Induction *)
Add LoadPath "./bin".
Require Export lesson1_Basics.

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

Check plus_n_Sm. 
Check plus_comm.
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
   rewrite -> plus_comm. reflexivity.
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
  simpl. rewrite -> plus_0_r. reflexivity. 
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
   SearchAbout negb.
   rewrite -> negb_involutive. reflexivity.
  rewrite -> add_neg.
  rewrite <- IHnn.
  reflexivity.
Qed.  



(**************************************************
  Exercise: 3 stars, optional (more_exercises)
  Take a piece of paper. For each of the following theorems, first think about whether (a) it can be proved using only simplification and rewriting, (b) it also requires case analysis (destruct), or (c) it also requires induction. Write down your prediction. Then fill in the proof. (There is no need to turn in your piece of paper; this is just to encourage you to reflect before hacking!)
**************************************************)


Theorem ble_nat_refl : forall n:nat,
                         true = ble_nat n n.
Proof.
  intros n. induction n as [|nn]. 
  simpl. reflexivity.
  simpl. rewrite <- IHnn. reflexivity. 
Qed.

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
 rewrite <- plus_comm. rewrite <- plus_assoc.
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
                         true = beq_nat n n.
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
  rewrite <- plus_comm. 
  replace (n + p) with (p + n). 
  rewrite -> plus_assoc. reflexivity. 
  rewrite -> plus_comm. reflexivity. 
Qed.

(**************************************************
  Exercise: 3 stars (binary_commute)
  Recall the increment and binary-to-unary functions that you wrote for the binary exercise in the Basics chapter. Prove that these functions commute — that is, incrementing a binary number and then converting it to unary yields the same result as first converting it to unary and then incrementing.

(Before you start working on this exercise, please copy the definitions from your solution to the binary exercise here so that this file can be graded on its own. If you find yourself wanting to change your original definitions to make the property easier to prove, feel free to do so.)
**************************************************)

Check inc_un_comm.



(**************************************************
  Exercise: 5 stars, advanced (binary_inverse) 
  This exercise is a continuation of the previous exercise about binary numbers. You will need your definitions and theorems from the previous exercise to complete this one.
**************************************************)

(* (a) First, write a function to convert natural numbers to binary numbers. Then prove that starting with any natural number, converting to binary, then converting back yields the same natural number you started with. *)

Check un_to_bin.

Theorem incbin_un : forall b, 
                      bin_to_un (incbin b) = S (bin_to_un b).
Proof.
  intros b. induction b as [|zero|one].
  simpl. reflexivity.
  simpl. reflexivity. 
  simpl. rewrite -> IHone. simpl. rewrite <- plus_n_Sm. reflexivity. 
Qed. 

Theorem nat_to_bin_back : forall n : nat,
                            bin_to_un (un_to_bin n) = n.
Proof. 
  intro n. induction n as [|nn].
  simpl. reflexivity.
  simpl. rewrite -> incbin_un. rewrite -> IHnn. reflexivity. 
Qed. 

(* (b) You might naturally think that we should also prove the opposite direction: that starting with a binary number, converting to a natural, and then back to binary yields the same number we started with. However, it is not true! Explain what the problem is. *)

(* Having problems with the base case, since there are "two ways" to represent zero *)
(* In fact, the biggest problem seems to be that are infinite ways of expressing numbers  *)
(* out of zeroes and ones. (thanks to cibele for pointing out that normalize needed to cover *)
(* all padding - not just this case!) this is a problem becuase we don't know if the zeroes *)
(* in the inductive case should actually be there and we could compare two numbers that are *)
(* structurally different but semantically the same *)

(* (c) Define a function normalize from binary numbers to binary numbers such that for any binary number b, converting to a natural and then back to binary yields (normalize b). Prove it.

Again, feel free to change your earlier definitions if this helps here. 
*)

(**
Definition normalize (b : bin) : bin := 
  un_to_bin (bin_to_un b).

Theorem normalized : forall (b : bin),
                       un_to_bin (bin_to_un  b) = (normalize b).
Proof.
  intros b. compute. reflexivity.
Qed.
**)

Definition iszero (n : nat) :=
match n with 
| O => true
| _ => false
end.

(** cibele's normalize function, with one small change  **)
Fixpoint normalize (b : bin) : bin := 
  match b with
  | inf => inf
  | one b' => one (normalize b')
  | zero b' => if iszero (bin_to_un b') then inf else zero (normalize b')
  end.

Example normalize_test1 : normalize (zero (zero (zero inf))) = inf.
Proof. simpl. reflexivity. Qed.
Example normalize_test2 : normalize (one (zero (zero inf))) = one inf.
Proof. simpl. reflexivity. Qed.
Example normalize_test3 : normalize (zero (one (zero (one inf)))) = zero (one (zero (one inf))).
Proof. simpl. reflexivity. Qed.

Theorem zero_incbin_comm : forall (b : bin),
                             zero (incbin b) = incbin (incbin (zero b)).
Proof.
  intros b.
  destruct b as [|bb|bb].
  Case "b is inf".
  simpl.
  reflexivity.
  Case "b is some zero bb".
  simpl.
  reflexivity.
  Case "b is some zero bb".
  simpl.
  reflexivity.
Qed.

Theorem one_incbin_comm : forall (b : bin),
                            one (incbin b) = incbin (incbin (incbin (zero b))).
Proof.
  intros b.
  destruct b as [|bb|bb].
  Case "b is inf".
  simpl.
  reflexivity.
  Case "b is some zero bb".
  simpl.
  reflexivity.
  Case "b is some one bb".
  simpl.
  reflexivity.
Qed.

Theorem uniqueness_of_0_l : forall (n m : nat),
                              n + m = 0 -> n = 0.
Proof.
  intros n m.
  destruct n as [|nn].
  reflexivity.
  intro H.
  inversion H.
Qed.

Theorem bin_zero : forall (b : bin),
                     bin_to_un b = 0 -> normalize b = inf.
Proof.
  intros b.
  induction b as [|bb|bb].
  Case "b is inf".
  simpl.
  reflexivity.
  Case "b is some zero bb".
  intro H.
  simpl in H.
  rewrite plus_0_r in H.
  apply uniqueness_of_0_l in H.
  simpl.
  rewrite H.
  reflexivity.
  Case "b is some one bb".
  intro H.
  inversion H.
Qed.

Lemma iszero_plus_and : forall a b,
                          iszero (a+b) = andb (iszero a) (iszero b).
Proof.
  intros a b.
  destruct a as [|aa].
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Lemma incbin_never_zero : forall b,
                            iszero (bin_to_un (incbin b)) = false.
Proof.
  induction b as [|b1|b2].
  Case "b is inf".
  simpl. reflexivity.
  Case "b is zero inf".
  simpl. reflexivity.
  Case "b is one inf".
  simpl. 
  rewrite plus_0_r.
  rewrite iszero_plus_and.
  rewrite IHb2.
  reflexivity.
Qed.

Theorem normalize_incbin_comm : forall (b : bin),
                                  normalize (incbin b) = incbin (normalize b).
Proof.
  intros b.
  induction b as [|bb|bb].
  Case "b is inf".
  simpl. reflexivity.
  Case "b is some zero bb".
  simpl.
  destruct (bin_to_un bb) as [|bb'] eqn:bin2un.
  SCase "(bin_to_un bb) is zero".
  simpl.
  apply bin_zero in bin2un.
  rewrite bin2un.
  reflexivity.
  SCase "(bin_to_un bb) is nonzero".
  simpl. reflexivity.
  Case "b is some one bb".
  simpl.
  rewrite incbin_never_zero.
  rewrite IHbb.
  reflexivity.
Qed.

Theorem double_bin : forall (n : nat),
                       un_to_bin (n + n) = normalize (zero (un_to_bin n)).
  intros m.
  induction m as [|mm].
  SSCase "n is zero".
  simpl. reflexivity.
  SSCase "n is some S mm".
  rewrite <- plus_n_Sm.
  rewrite plus_comm.
  rewrite <- plus_n_Sm.
  (* trying to avoid unfolding normalize *)
  assert (left_side : un_to_bin (S (S (mm+mm))) = incbin (incbin (un_to_bin (mm+mm)))).
   simpl. reflexivity.
  rewrite left_side.
  assert (right_side : un_to_bin (S mm) = incbin (un_to_bin mm)).
   simpl. reflexivity.
  rewrite right_side.
  rewrite zero_incbin_comm.
  rewrite IHmm.
  rewrite <- normalize_incbin_comm.
  rewrite <- normalize_incbin_comm.
  reflexivity.
Qed.

Theorem bin_to_un_normalize : forall  b,
                                bin_to_un (normalize b) = bin_to_un b.
Proof.
  intros b. induction b as [|bb|bb].
  simpl. reflexivity.
  simpl. rewrite plus_0_r. destruct (bin_to_un bb) as [|nn] eqn:asun.
  simpl. reflexivity.
  simpl. rewrite plus_0_r. rewrite IHbb. simpl. reflexivity.
  simpl. rewrite plus_0_r. rewrite plus_0_r. rewrite IHbb. reflexivity.
Qed.

Theorem normalize_idempotence : forall b, 
                                  normalize (normalize b) = normalize b.
Proof. 
  intros b. induction b as [|bb|bb].
  Case "b is inf".
  simpl. reflexivity.
  Case "b is zero bb".
  simpl. destruct (iszero (bin_to_un bb)) eqn:pred.
  simpl. reflexivity.
  simpl. rewrite bin_to_un_normalize. rewrite pred. rewrite IHbb. reflexivity.
  Case "b is one bb".
  simpl. rewrite IHbb. reflexivity.
Qed.

Theorem normalized : forall (b : bin),
                       un_to_bin (bin_to_un b) = (normalize b).
Proof.
  intros b. induction b as [|bb|bb].
  Case "b is inf".
  simpl. reflexivity.
  Case "b is some zero bb".
  simpl. destruct (bin_to_un bb) as [|n].
  SCase "(bin_to_un bb) is 0".
  simpl. reflexivity.
  SCase "(bin_to_un bb) is some S n".
  rewrite plus_0_r.
  rewrite <- IHbb.
  simpl.
  rewrite <- plus_n_Sm.
  simpl.
  assert (Lem1 : forall m, incbin (un_to_bin m) = un_to_bin (S m)).
    intros m. induction m as [|mm].
    simpl. reflexivity.
    simpl. reflexivity.
  rewrite Lem1.
  rewrite Lem1.
  rewrite plus_n_Sm.
  rewrite <- plus_Sn_m.
  rewrite double_bin.
  simpl.
  rewrite incbin_never_zero.
  rewrite normalize_incbin_comm.
  assert (Lem2 : forall m, normalize (un_to_bin m) = un_to_bin m).
    intros m. induction m as [|mm].
    simpl. reflexivity.
    simpl. rewrite normalize_incbin_comm. rewrite IHmm. reflexivity.
  rewrite Lem2.
  reflexivity.
  Case "b is some one bb".
  simpl.
  rewrite plus_0_r.
  rewrite double_bin.
  rewrite IHbb.
  rewrite <- normalize_incbin_comm.
  simpl. rewrite normalize_idempotence. reflexivity.
Qed.

(**************************************************
Exercise: 2 stars, advanced (plus_comm_informal)
Translate your solution for plus_comm into an informal proof.
**************************************************)
(***

Theorem: Addition is commutative (for any natural numbers n and m, 
 n + m = m + n
Proof: By induction on n.

  Base case: n=0. 
  Substituting the base case for n, we get 0 + m = m + 0. 
  By the additive identity, we can rewrite this to m = m, which is true by reflexivity.

  Inductive hypothesis: Assume n + m = m + n.
  Show that (S n) + m = m + (S n). We will derive the expression on the right from the left.
  By the definition of unary increment, we can rewrite the left hand side as (n + S O) + m. 
  By associativity, we can express this as n + (S O + m). We have previously shown that adding
  one is commutative, so we can apply commutativity to the second sum and then apply our rewrite rule for sums:
  n + S (m + O). By additive identity and our definition of addition, we can say that n + S (m + O) = S (n + m).
  Applying the inductive hypothesis, we get S (m + n). Applying our definition of addition again, we obtain our 
  result. 
***)



(**************************************************
Exercise: 2 stars, optional (beq_nat_refl_informal)
Write an informal proof of the following theorem, using the informal proof of plus_assoc as a model. Don't just paraphrase the Coq tactics into English!
**************************************************)

(***
Theorem: true = beq_nat n n for any n.
Proof: By cases. 
  First let n=0. Clearly beq_nat 0 0 evaluates to true. 
  Now let n be some number greater than zero. beq_nat operates over the structure of the number; it compares
  two numbers on the basis of the number of recursive steps it takes. If one number reaches zero before the other,
  this means that one number must have more S's than the other and thus are not equal. 
  Since the two arguments are identical, they must be composed of identical S's and therefore
  must terminate in equal steps. Since this is the condition for equality, we can say that beq_nat n n for any
  n must be true.
***)