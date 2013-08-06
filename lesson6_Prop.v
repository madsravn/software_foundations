(* Software Foundations Chapter 6 : Propositions and Evidence *)
Add LoadPath "./bin".
Require Export MoreCoq.
Require Import lesson1_Basics.
Require Import lesson2_Induction.
Require Import lesson3_Lists.
Require Import lesson4_Poly.



(**************************************************
  Exercise: 2 stars (b_timesm)
**************************************************)

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem b_timesm: forall n m, 
                    beautiful n ->  beautiful (m*n).
Proof.
  intros n m.
  induction m as [|mm].
  Case "m is zero".
  simpl.
  intros H.
  apply b_0.
  Case "m is some S mm".
  rewrite -> mult_comm.
  rewrite <- mult_n_Sm.
  intro H.
  apply b_sum.
  rewrite -> mult_comm.
  apply IHmm.
  apply H.
  apply H.
Qed.



(**************************************************
  Exercise: 1 star (gorgeous_tree)
  Write out the definition of gorgeous numbers using inference rule notation.
**************************************************)

(**
                    ------------ (g_0)
                     gorgeous n


  
      gorgeous n                 gorgeous n
  ------------------ (g_3)    ----------------- (g_5)
   gorgeous (3 + n)            gorgeous (5 + n)


**)





(**************************************************
  Exercise: 1 star (gorgeous_plus13)
 **************************************************)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).


Theorem gorgeous_plus13: forall n, 
                           gorgeous n -> gorgeous (13+n).
Proof.
  intros n E.
  induction E as [|nn|nn].
  Case "n is zero".
  simpl.
  apply g_plus3.
  apply g_plus5.
  apply g_plus5.
  apply g_0.
  rewrite plus_comm with (n:=3) (m:=nn).
  rewrite plus_assoc.
  rewrite plus_comm.
  apply g_plus3.
  apply IHE.
  rewrite plus_comm with (n:=5) (m:=nn).
  rewrite plus_assoc.
  rewrite plus_comm.
  apply g_plus5.
  apply IHE.
Qed.



(**************************************************
  Exercise: 2 stars (gorgeous_sum)
 **************************************************)

Theorem gorgeous_sum : forall n m,
                         gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m E1 E2.
  induction E1 as [|nn|nn].
  Case "gorgeous n base case : n is zero".
  simpl.
  apply E2.
  Case "gorgeous n IStep1 -> n is 3 + nn".
  rewrite <- plus_assoc.
  apply g_plus3.
  apply IHE1.
  Case "gorgeous n IStep2 -> n is 5 + nn".
  rewrite <- plus_assoc.
  apply g_plus5.
  apply IHE1.
Qed.



(**************************************************
  Exercise: 3 stars, advanced (beautiful__gorgeous)
 **************************************************)
Theorem beautiful__gorgeous : forall n, 
                                beautiful n -> gorgeous n.
Proof.
  intros n E.
  induction E as [ | | |nn].
  Case "n is zero".
  apply g_0.
  Case "n is three".
  rewrite <- plus_0_r.
  apply g_plus3.
  apply g_0.
  Case "n is five".
  rewrite <- plus_0_r.
  apply g_plus5.
  apply g_0.
  Case "beautiful (nn + m)".
  apply gorgeous_sum.
  apply IHE1.
  apply IHE2.
Qed.



(**************************************************
  Exercise: 3 stars, optional (g_times2)
  Prove the g_times2 theorem below without using gorgeous__beautiful. You might find the following helper lemma useful.
**************************************************)

Lemma helper_g_times2 : forall x y z, 
                          x + (z + y)= z + x + y.
Proof.
  intros x y z.
  rewrite plus_assoc.
  rewrite plus_comm with (n:=x) (m:=z).
  reflexivity.
Qed.

Theorem g_times2: forall n, 
                    gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl.
   induction H.
   Case "gorgeous 0".
   simpl.
   apply g_0.
   Case "gorgeous (3+n)".
   rewrite plus_0_r in IHgorgeous.
   rewrite plus_0_r.
   rewrite <- plus_assoc.
   apply g_plus3.
   rewrite helper_g_times2.
   rewrite <- plus_assoc.
   apply g_plus3.
   apply IHgorgeous.
   Case "gorgeous (5+n)".
   rewrite plus_0_r in IHgorgeous.
   rewrite plus_0_r.
   rewrite <- plus_assoc.
   apply g_plus5.
   rewrite helper_g_times2.
   rewrite <- plus_assoc.
   apply g_plus5.
   apply IHgorgeous.
Qed.

(**************************************************
**************************************************
**************************************************)