Add Rec LoadPath "/home/etosch/dev/proofs".
Add Rec LoadPath "/home/etosch/dev/proofs/sf".
Require Import lesson3.

Theorem silly_ex : 
 forall n, evenb n = true -> 
            oddb (S n) = true -> 
             evenb 3 = true ->
              oddb 4 = true.
Proof.
 intro n.
 intros assumption1 assumption2 assumption3. 
 apply assumption3. 
Qed.
 (* whaaaaa??? *)

Theorem rev_exercise1 : forall (l ll : list nat),
 l = rev ll -> ll = rev l.
Proof. 
 intros l ll H1. symmetry. rewrite -> H1.
 SearchAbout rev. 
 apply rev_involutive. 
Qed. 

(* Exercise: 1 star (apply_rewrite)
Briefly explain the difference between the tactics apply and 
rewrite. Are there situations where both can usefully be applied? *)

(* rewrite specifies the direction? is apply only unidirectional? *)

Theorem beq_nat_refl : forall (n : nat),
 beq_nat n n = true.
Proof. 
 induction n as [|nn]. reflexivity. simpl. apply IHnn. 
Qed. 

Theorem override_eq : forall {X : Type} x k (f : nat -> X),
 (override f k x) k = x.
Proof. 
 intros X x k f. unfold override. rewrite -> beq_nat_refl. reflexivity. 
Qed. 

Theorem eq_add_S : forall n m : nat,
 S n = S m -> n = m.
Proof. 
 intros n m H1. inversion H1. reflexivity. 
Qed. 

Theorem eq_remove_S : forall n m : nat,
 n = m -> S n = S m.
Proof.
 intros n m eq. inversion eq. reflexivity.
Qed. 

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j assumption1 assumption2. 
  inversion assumption1. 
  inversion assumption2.
  symmetry. 
  apply H0. 
Qed. 

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
 x :: y :: l = [] ->
  y :: l = z :: j ->
   x = z. 
Proof. 
 intros X x y z l j allemptyOrFalse zjEmptyOrZIsHead.
 inversion allemptyOrFalse.
Qed.

Require Import lesson1. 
Require Import lesson2.

Theorem length_snoc' : forall (X : Type) (v : X) (l : list X) (n : nat),
 length l = n -> length (snoc l v) = S n.
Proof. 
 intros X v l. induction l as [| h t].
 Case "l=[]".  intros n eq. rewrite <- eq. simpl. reflexivity. 
 Case "l=v'::l". intros n eq. simpl. destruct n as [| nn]. simpl.
  SCase "n=0". inversion eq. 
  SCase "n=Sn'". apply eq_remove_S. apply IHt. inversion eq. reflexivity. 
Qed. 

Theorem beq_nat_eq_FAILED : forall n m, 
 true = beq_nat n m -> n = m.
Proof. 
 intros n. induction n as [| nn]. 
 Case "n = 0". intros m. destruct m as [| mm].
  SCase "m = 0". reflexivity. 
  SCase "m = S mm". simpl. intro H. inversion H. 
 Case "n = S nn". intro m. destruct m as [| mm].
  SCase "m = 0". simpl. intro H. inversion H. 
  SCase "m = S mm". simpl. intro H. apply eq_remove_S. apply IHnn. apply H. 
Qed. 

(* note that calling apply IHnn dealt with the implication in its entirety. Calling rewrite generated a new subgoal *)
Theorem beq_nat_eq' : forall m n,
 beq_nat n m = true -> n = m. 
Proof. 
 intros m. induction m as [| mm].
 intros n. induction n as [| nn]. 
 reflexivity. 
 intro H. inversion H. 
 intro n. induction n as [| nn].
 intro H. inversion H. 
 intro H. apply eq_remove_S. simpl in H. apply IHmm. apply H. 
Qed. 

Theorem beq_nat_0_l : forall n,
 true = beq_nat 0 n -> 0 = n.
Proof. 
 intros n. 
 destruct n as [|nn].
 reflexivity. 
 simpl. intro H. inversion H.
Qed. 

Theorem beq_nat_0_r : forall n,
 true = beq_nat n 0 -> 0 = n. 
Proof. 
 intros n. 
 destruct n as [| nn].
 reflexivity. 
 simpl. intro H. inversion H. 
Qed. 

Theorem beq_nat_sym : forall n m : nat,
 beq_nat n m = beq_nat m n.
Proof. 
 intros n. induction n as [| nn].
 intro m. destruct m as [| mm].
 reflexivity. 
 simpl. reflexivity. 
 intro m. destruct m as [| mm].
 simpl. reflexivity.
 apply IHnn.
Qed.

Theorem silly3' : forall n : nat,
 (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
   true = beq_nat n 5 ->
     true = beq_nat (S (S n)) 7. 
Proof.
 intros n eq H.
 symmetry in H. apply eq in H. (*  p -> q -> r. uses p -> q to isolate r *)
 symmetry in H. apply H. 
Qed. 

Theorem plus_n_n_injective : forall n m : nat,
 n + n = m + m -> n = m.
Proof.
 intros n. induction n as [| nn].
 destruct m as [|mm].
 reflexivity.
 intro H. inversion H.
 destruct m as [| mm].
 intro H. inversion H. 
 intro H. inversion H. rewrite <- plus_n_Sm in H1. rewrite <- plus_n_Sm in H1. 
  apply eq_add_S in H1. apply IHnn in H1.
  apply eq_remove_S. apply H1.
Qed.

Theorem override_shadow: forall {X:Type} x1 x2 k1 k2 (f : nat -> X),
 (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2. 
Proof.
 intros X x1 x2 k1 k2 f.
 unfold override. 
 destruct (lesson3.beq_nat k1 k2).
 Case "beq_nat k1 k2 = true". reflexivity. (* why does this need the Top part? *)
 Case "beq_nat k1 k2 = false". reflexivity. 
Qed.

Definition tl {X:Type} (l : list X) : list X :=
 match l with
 | [] => []
 | h::t => t
 end.

Example trans_eq_example : forall a b c d e f : nat, [a,b] = [c,d] -> [c,d] = [e,f] -> [a,b] = [e,f].
Proof. intros a b c d e f eq1 eq2. rewrite -> eq1. rewrite -> eq2. reflexivity. Qed.
 

Theorem trans_eq : forall {X : Type} (n m o : X),
                     n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity. 
Qed.

Example trans_eq_example' : forall a b c d e f : nat, 
                             [a,b] = [c,d] -> [c,d] = [e,f] -> [a,b] = [e,f].
Proof. 
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c,d]).
  apply eq1. apply eq2.   
Qed.   

Definition minustwo (n : nat) :=
match n with
| O => O
| S O => O
| S (S n) => n
end.

Example trans_eq_exercise : forall m n o p : nat,
                              m = (minustwo o) -> 
                              (n + p) = m ->
                              (n + p) = (minustwo o).

Proof. 
  intros m n o p.
  intros eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed. 

(*
Example trans_eq_exercise' : forall m n o p : nat,
                              m = (minustwo o) ->
                              (n + p) = m ->
                              (n + p) = (minustwo o).
*)


Theorem silly4 : forall n m : nat,
                   [n]=[m] -> n = m.
Proof. 
  intros n m. 
  intro H. 
  inversion H. 
  reflexivity. 
Qed.

Theorem silly5 : forall n m o : nat,
                   [n,m] = [o,o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity. 
Qed.

Theorem silly6 : forall n : nat,
                   S n = O -> 2 + 2 = 5.
Proof.
  intros n.
  intro H. inversion H. 
Qed.

Theorem silly7 : forall n m : nat,
                   false = true -> [n] = [m].
Proof. 
  intros n m.
  intro H. inversion H.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
                    x = y -> f x = f y.
Proof.
  intros A B f x y.
  intro H. (* can't do apply here *)
  rewrite H. reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
                         beq_nat n m = true -> n = m.
Proof.
  intro n.
  induction n as [| nn].
  destruct m as [| mm].
  simpl. reflexivity. 
  simpl. intro H. inversion H.
  intros m H.
(* come back to this later *)
Admitted.  



(* Theorem S_inj : forall (n m : nat) (b : bool),
                  beq_nat (S n) (S m ) = b ->
                  *) 