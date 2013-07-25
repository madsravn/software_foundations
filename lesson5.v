Add Rec LoadPath "/home/etosch/dev/proofs".
Add Rec LoadPath "/home/etosch/dev/proofs/sf".
Require Import lesson1.
Require Import lesson4. 


  Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule b_3. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by b_sum, we must provide
      evidence of beautiful 3 and beautiful 5. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

Theorem beautiful_plus_eight:  forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n H.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply H. 
Qed. 

(*Exercise: 2 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n ->  beautiful (m*n).
Proof.
  intros n m H. induction m as [|mm].
  simpl. apply b_0.
  assert (S mm * n = n * S mm).
   apply mult_comm.
  rewrite -> H0.
  Check mult_m_Sn.
  rewrite -> mult_m_Sn.
  apply b_sum with (n:=n*mm) (m:=n).
  rewrite -> mult_comm.
  apply IHmm. 
  apply H.
Qed.

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0 
| g_plus3 : forall n, gorgeous n -> gorgeous (3 + n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5 + n).

Theorem gorgeous_plus13 : forall n,
                            gorgeous n -> gorgeous (13 + n).
Proof. 
  intros n H. 
  assert (H1 : gorgeous (10 + n)).
  assert (H2 : gorgeous (5 + n)).
  apply g_plus5. apply H.
  assert (H3 : gorgeous (10 + n) = gorgeous (5 + (5 + n))). reflexivity. 
  rewrite -> H3. apply g_plus5 with (n:=(5+n)). apply g_plus5. apply H.
  assert (H4 : gorgeous (13 + n) = gorgeous (3 + (10 + n))). reflexivity.
  rewrite -> H4. apply g_plus3 with (n:=(10+n)). apply H1. 
Qed. 

Theorem gorgeous_beautiful : forall n,
                               gorgeous n -> beautiful n.
Proof. 
  intros n H. 
  induction H as [|g3|g5].
  Case "g_0". apply b_0.
  Case "g_plus3". apply b_sum. apply b_3. apply IHgorgeous.
  Case "g_plus5". apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

Theorem gorgeous_sum : forall n m,
                         gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof. 
  intros n m H1 H2. induction H1 as [|g3|g5].
  simpl. apply H2. 
  apply g_plus3 with (n:=(g3+m)). apply IHgorgeous. 
  apply g_plus5 with (n:=(g5+m)). apply IHgorgeous. 
Qed. 

Theorem beautiful_gorgeous : forall n, 
                               beautiful n -> gorgeous n.
Proof. 
  intros n H.
   assert (Hg0 : gorgeous 0). apply g_0.
  induction H as [|b3|b5|bsum].
  Case "b0". apply g_0. 
  Case "b3". rewrite <- plus_0_r. apply g_plus3. apply g_0. 
  Case "b5". rewrite <- plus_0_r. apply g_plus5. apply g_0.
  Case "bsum". apply gorgeous_sum with (n:=bsum) (m:=m). apply IHbeautiful1. apply IHbeautiful2. 
Qed. 

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y. 
Proof. 
  intros x y z. 
  rewrite <- assoc_add. assert (H : x + z = z + x). apply plus_comm. 
  rewrite -> H. reflexivity. 
Qed.

Theorem double : forall n, 2*n = n + n. 
Proof. 
  intros n. destruct n as [|nn].
  simpl. reflexivity.
  simpl. apply eq_remove_S. 
  rewrite -> plus_0_r. reflexivity. 
Qed.   


Theorem g_times2 : forall n, gorgeous n -> gorgeous (2 * n). 
Proof. 
  intros n H.
  assert (H1 : 2 * n = n + n). apply double.
  rewrite -> H1. apply gorgeous_sum. apply H. apply H. 
Qed. 

(* Propositions *)
Definition even (n : nat) : Prop :=
  evenb n = true.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n)). 

Theorem double_even : forall n,
                        ev (2 * n). 
Proof. 
  intro n. induction n as [|nn].
  simpl. apply ev_0.
  rewrite -> double in IHnn. 
  rewrite -> double. simpl. rewrite <- plus_n_Sm. apply ev_SS. apply IHnn. 
Qed.

Theorem ev_even : forall n,
                    ev n -> even n.
Proof. 
  intros n E. induction E as [| nn EE].
  Case "E=ev_0". unfold even. reflexivity. 
  Case "E=ev_SS nn EE". unfold even. apply IHEE. 
Qed. 
(*
Theorem ev_even' : forall n,
                     ev n -> even n.
Proof. 
  intros n E. induction n as [|nn].
  Case "n = 0". unfold even. reflexivity. 
  Case "n = S nn". unfold even. 
The problem here is that I get to a point where I want to destruct the possibilities,
but since the proposition is not inductively defined, I can't *)

Theorem ev_sum : forall n m, 
                   ev n -> ev m -> ev (n+m).

  intros n m H1. induction H1 as [|e1].
  Case "n=0". intro H. simpl. apply H. 
  Case "n=SSnn". intro H2. destruct H2 as [|e2].
   SCase "m=0". rewrite -> plus_0_r in IHev. rewrite -> plus_0_r. apply ev_SS. apply H1. 
   SCase "m=SSmm". rewrite -> plus_comm. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. apply ev_SS. rewrite -> plus_comm. apply IHev. apply ev_SS. apply H2. 
Qed. 

Theorem ev_minus2 : forall n,
                      ev n -> ev (pred (pred n)). 
Proof. 
  intros n E. 
  inversion E as [| zero ss].
  simpl. apply ev_0. 
  simpl. apply ss. 
Qed. 

Theorem SSev_even : forall n,
                      ev (S (S n)) -> ev n.
Proof. 
  intros n E. 
  inversion E as [|zero ss]. 
  apply ss. 
Qed.

Theorem SSSSev_even : forall n,
                        ev (S (S (S (S n)))) -> ev n.
Proof. 
  intros n E. inversion E. apply SSev_even. apply H0. 
Qed. 

Theorem even5_nonsense : ev 5 -> 2 + 2 = 9.
Proof. 
  intro E. inversion E. inversion H0. inversion H2. 
Qed. 

Theorem uniqueness_of_zero_l : forall n m,
                               n + m = 0 -> n = 0.
Proof. 
  intros n m. destruct n as [|nn]. destruct m as [|mm]. 
  reflexivity.
  simpl. intro H. inversion H. 
  destruct m as [| mm].
  simpl. intro H. inversion H. 
  intro H. inversion H. 
Qed.

Theorem uniqueness_of_zero_r : forall n m, 
                                 n + m = 0 -> m = 0.
Proof. 
  intros n m. assert (n+m=m+n). apply plus_comm.
  rewrite -> H. apply uniqueness_of_zero_l.
Qed.
  
Theorem ev_ev__ev : forall n m,
                      ev (n + m) -> ev n -> ev m.
Proof.
  intros n m H1.
  inversion H1 as [zed|ss].
  intro H2. 
  symmetry in zed. apply uniqueness_of_zero_r in zed. rewrite -> zed. apply ev_0.
  intro H2. 