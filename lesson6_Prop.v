(* Software Foundations Chapter 6 : Propositions and Evidence *)
Add LoadPath "./bin".
Require Export MoreCoq.
Require Export lesson3_Lists.




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
  Exercise: 1 star (double_even)
 **************************************************)

Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n:nat, 
            ev n -> ev (S (S n)).

Theorem double_even : forall n,
                        ev (double n).
Proof.
  intros n.
  induction n as [|nn].
  simpl.
  apply ev_0.
  simpl.
  apply ev_SS.
  apply IHnn.
Qed.



(**************************************************
  Exercise: 1 star (ev__even)
  Here is a proof that the inductive definition of evenness implies the computational one.
 **************************************************)

Definition even (n:nat) : Prop := 
  evenb n = true.

Theorem ev__even : forall n,
                     ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0".
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".
    unfold even. apply IHE'.
Qed.

(**
  Could this proof also be carried out by induction on n instead of E? If not, why not?
**)

(**
  No - if we use induction on n, we end up having to consider ev (S n). We cannot determine whether S n is even or odd from the form given and have no further evidence for it. Furthermore, we have no mechanism for pulling out the S from ev (S n), and so we cannot apply the inductive hypothesis in any way.
**)



(**************************************************
  Exercise: 1 star (l_fails)
  The following proof attempt will not succeed.
     Theorem l : ∀n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
  Intuitively, we expect the proof to fail because not every number is even. However, what exactly causes the proof to fail?
 **************************************************)

(**
  This fails for the same reason as the previous problem.
**)


(**************************************************
Exercise: 2 stars (ev_sum)
Here's another exercise requiring induction.
**************************************************)
Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof.
  intros n m E1 E2.
  induction E1 as [| nn E].
  Case "ev n is ev_0".
  destruct E2 as [|mm E'].
  SCase "ev m is ev_0".
  simpl.
  apply ev_0.
  SCase "ev m is some ev mm, called E'".
  simpl.
  apply ev_SS.
  apply E'.
  Case "ev_n is some ev nn, called E".
  destruct E2 as [|mm E'].
  rewrite plus_0_r.
  rewrite plus_0_r in IHE.
  apply ev_SS.
  apply IHE.
  rewrite plus_comm.
  rewrite <- plus_n_Sm.
  rewrite <- plus_n_Sm.
  apply ev_SS.
  rewrite plus_comm.
  apply IHE.
Qed.



(**************************************************
  Exercise: 1 star, optional (ev_minus2_n)
  What happens if we try to use destruct on n instead of inversion on E?
 **************************************************)
Theorem ev_minus2: forall n,
                     ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0.
  Case "E = ev_SS n' E'". simpl. apply E'. Qed.

(** 
  inversion on E gives us some S (S n) to work with. If we destruct, we only get some S n. We can strip the first S with pred, but we will be left with an extra pred and have no way of reducing it to something over which we can apply evidence.
**)



(**************************************************
  Exercise: 1 star (inversion_practice)
 **************************************************)
Theorem SSSSev__even : forall n,
                         ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [|nn E1].
  inversion E1 as [|nn' E2].
  apply E2.
Qed.

(**
  The inversion tactic can also be used to derive goals by showing the absurdity of a hypothesis.
**)

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof.
  intro E.
  inversion E as [|n0 E1].
  inversion E1 as [|n1 E2].
  inversion E2 as [|n2 E3].
Qed.



(**************************************************
  Exercise: 3 stars, advanced (ev_ev__ev)
  Finding the appropriate thing to do induction on is a bit tricky here:
 **************************************************)
Theorem ev_ev__ev : forall n m,
                      ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Enm En.
  induction En.
  Case "ev n is ev 0".
  simpl in Enm.
  apply Enm.
  Case "ev n is ev (S (S n))".
  apply IHEn.
  rewrite plus_comm in Enm.
  rewrite <- plus_n_Sm in Enm.
  rewrite <- plus_n_Sm in Enm.
  apply ev_minus2 in Enm.
  simpl in Enm.
  rewrite <- plus_comm in Enm.
  apply Enm.
Qed.



(**************************************************
  Exercise: 3 stars, optional (ev_plus_plus)
  Here's an exercise that just requires applying existing lemmas. No induction or even case analysis is needed, but some of the rewriting may be tedious.
**************************************************)

Theorem ev_plus_plus : forall n m p,
                         ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Enm Enp.
  generalize Enm.
  apply ev_ev__ev.
  rewrite plus_comm.
  rewrite <- plus_assoc.
  rewrite plus_comm.
  rewrite plus_assoc.
  rewrite <- plus_assoc with (n:=p+n) (m:=m) (p:=m).
  rewrite plus_comm with (n:=p) (m:=n).
  rewrite plus_comm with (n:=n+p) (m:=m+m).
  generalize Enp.
  apply ev_sum with (m:=n+p) (n:=m+m).
  rewrite <- double_plus.
  apply double_even.
Qed.  



(**************************************************
  Exercise: 4 stars (palindromes)
  A palindrome is a sequence that reads the same backwards as forwards.
  
  Define an inductive proposition pal on list X that captures what it means to be a palindrome. (Hint: You'll need three cases. Your definition should be based on the structure of the list; just having a single constructor

  c : ∀l, l = rev l → pal l

  may seem obvious, but will not work very well.)

Prove that
   
  ∀l, pal (l ++ rev l).

Prove that
 
  ∀l, pal l → l = rev l.
**************************************************)


Inductive pal : list Type -> Prop :=
  empty : pal []
| odd_list : forall x l,  pal (l ++ (x :: (rev l)))
| even_list : forall l,  pal (l++(rev l)).

Theorem pal_app_rev : forall l,
                         pal (l++(rev l)).
Proof.
  intros l.
  apply even_list.
Qed.

Theorem app_nil : forall X (l : list X),
                    l ++ [] = l.
Proof.
  intros X l.
  induction l as [|h t].
  simpl. reflexivity.
  simpl. rewrite IHt. reflexivity.
Qed.

Theorem snoc_append : forall X (l:list X) n,
                        snoc l n = l ++ [n].
Proof.
 intros X l n. induction l as [| nn ll]. reflexivity. 
 simpl. rewrite <- IHll. reflexivity. 
Qed. 

Theorem app_right : forall X (l1 l2 l3 : list X),
                      l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros X m1 m2 m3. induction m1 as [|h1 t1]. 
  reflexivity. 
  simpl. rewrite -> IHt1. reflexivity.
Qed.

Theorem distr_rev : forall X (l1 l2 : list X),
                      rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof. 
  intros X l1 l2.
  induction l1 as [| h1 t1].
  Case "l1 is nil".
  simpl. 
  rewrite -> app_nil. 
  reflexivity. 
  Case "l1 is some h::t".
  simpl. 
  rewrite -> snoc_append. 
  rewrite -> IHt1. 
  rewrite -> snoc_append. 
  rewrite -> app_right.
  reflexivity. 
Qed.

Theorem pal_is_rev : forall l,
                       pal l -> l = rev l.
Proof.
  intros l H.
  inversion H as [ E|x lst E|lst E].
  Case "the palandrome is empty".
  simpl.
  reflexivity.
  Case "the palandrome has an odd number of elts".
  destruct lst as [|h t].
  SCase "l is empty".
  simpl.
  reflexivity.
  SCase "l is some h::t".
  simpl.
  rewrite distr_rev.
  simpl.
  rewrite rev_snoc.
  rewrite rev_involutive.
  rewrite snoc_with_append.
  SearchAbout snoc.
  assert (Lem1 : forall ll, snoc (h::t) x ++ ll = (h::t)++[x]++ll).
    intros ll.
    rewrite snoc_append.
    rewrite app_right.
    reflexivity.
  rewrite Lem1.
  simpl.
  reflexivity.
  Case "the palandrome has an even number of elts".
  rewrite distr_rev.
  rewrite rev_involutive.
  reflexivity.
Qed.



(**************************************************
Exercise: 5 stars, optional (palindrome_converse)
Using your definition of pal from the previous exercise, prove that
     ∀l, l = rev l → pal l.
**************************************************)

Theorem snoc_rev : forall X (h : X) t,
                    snoc t h = rev (h::rev t).
Proof.
  intros X h t.
  simpl.
  rewrite rev_involutive.
  reflexivity.
Qed.

Theorem pal_helper : forall l x,
                       pal l -> pal (x :: (snoc l x)).
Proof.
  intros l x H.
  inversion H as [E| xx ll odd| ll even].
  Case "l is the empty palindrome".
  simpl.
  assert (Lem1 : forall X (h : X) t,
                   h::t = [h] ++ t).
   intros X h t.
   simpl.
   reflexivity.
  rewrite Lem1.
  apply even_list.
  Case "l is the odd palindrome".
  rewrite snoc_with_append.  
  simpl.
  rewrite snoc_rev.
  rewrite rev_involutive.
  apply odd_list with (x:=xx) (l:=x::ll).
  Case "l is the even palindrome".
  rewrite snoc_with_append.
  rewrite snoc_rev.
  rewrite rev_involutive.
  apply even_list with (l:=x::ll).
Qed.

Theorem palindrome_converse : forall l,
                                l = rev l -> pal l.
Proof.
  intros l H.
  destruct l as [|h t].
  Case "l is the empty list".
  apply empty.
  Case "l is some h::t".
  
  
  

(**************************************************
Exercise: 4 stars, advanced (subsequence)
A list is a subsequence of another list if all of the elements in the first list occur in the same order in the second list, possibly with some extra elements in between. For example,
    [1,2,3]
is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
but it is not a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]
Define an inductive proposition subseq on list nat that captures what it means to be a subsequence. (Hint: You'll need three cases.)
Prove that subsequence is reflexive, that is, any list is a subsequence of itself.
Prove that for any lists l1, l2, and l3, if l1 is a subsequence of l2, then l1 is also a subsequence of l2 ++ l3.
(Optional, harder) Prove that subsequence is transitive — that is, if l1 is a subsequence of l2 and l2 is a subsequence of l3, then l1 is a subsequence of l3. Hint: choose your induction carefully!
**************************************************)


(**************************************************
Exercise: 2 stars, optional (R_provability)
Suppose we give Coq the following definition:
    Inductive R : nat → list nat → Prop :=
      | c1 : R 0 []
      | c2 : ∀n l, R n l → R (S n) (n :: l)
      | c3 : ∀n l, R (S n) l → R n l.
Which of the following propositions are provable?
R 2 [1,0]
R 1 [1,2,1,0]
R 6 [3,2,1,0]
**************************************************)