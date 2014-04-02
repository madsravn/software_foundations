Add LoadPath "./sf".
Require Export SfLib.

Module AExp.

Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue : bexp
| BFalse : bexp
| BNot : bexp -> bexp 
| BLe : aexp -> aexp -> bexp
| BEq : aexp -> aexp -> bexp
| BAnd : bexp -> bexp -> bexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Fixpoint beval (b : bexp) : bool :=
  match b with 
    | BTrue => true
    | BFalse => false
    | BNot bb => negb (beval bb)
    | BLe x y => ble_nat (aeval x) (aeval y)
    | BEq x y => beq_nat (aeval x) (aeval y)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a : aexp) : aexp :=
  match a with 
    | ANum n => ANum n
    | APlus (ANum 0) e => optimize_0plus e
    | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
    | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
    | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Theorem optimize_0plus_sound : forall a, 
                                 aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a as [n|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2].
  Case "ANum". reflexivity.
  Case "APlus".
    destruct e1.
    SCase "a1 is ANum".
      destruct n. 
      SSCase "n = 0".
        simpl. rewrite IHe2. reflexivity.
      SSCase "n<>0".
        simpl. rewrite IHe2. reflexivity.
    SCase "a1 is APlus".
    simpl. simpl in IHe1. rewrite IHe1. (* not sure what's being matched here *)
    rewrite IHe2. reflexivity.
    SCase "a1 is AMinus".
    simpl. rewrite IHe2. simpl in IHe1. rewrite IHe1. reflexivity.
    SCase "a1 is AMult".
    simpl. rewrite IHe2. simpl in IHe1. rewrite IHe1. reflexivity.
  Case "AMinus".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
    simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(* consider using repeat, try, ; *)

Theorem optimize_0plus_sound' : forall a,
                                  aeval (optimize_0plus a) = aeval a.
Proof. 
  intros a.
  induction a as [n|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2|e1 IHe1 e2 IHe2];
    try (simpl; rewrite IHe1; rewrite IHe2 ; reflexivity).
  Case "ANum".
  induction n as [|nn]. reflexivity. reflexivity.
  Case "APlus".
  destruct e1;
    try (simpl; simpl in IHe1; rewrite IHe1; rewrite IHe2; reflexivity).
  SCase "APlus, ANum".
  destruct n; simpl; rewrite IHe2; reflexivity.
Qed.

Theorem optimize_0plus_sound'' : forall a,
                                   aeval (optimize_0plus a) = aeval a.
Proof. 
  intros a.
  induction a;
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    try reflexivity.
  Case "APlus a1 a2".
  destruct a1; 
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
  destruct n; simpl; rewrite IHa2; reflexivity.
Qed.




(**************************************************
Exercise: 3 stars (optimize_0plus_b)
Since the optimize_0plus tranformation doesn't change the value of aexps, we should be able to apply it to all the aexps that appear in a bexp without changing the bexp's value. Write a function which performs that transformation on bexps, and prove it is sound. Use the tacticals we've just seen to make the proof as elegant as possible.
**************************************************)

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
    | BLe x y => BLe (optimize_0plus x) (optimize_0plus y)
    | BEq x y => BEq (optimize_0plus x) (optimize_0plus y)
    | _ => b
  end.

Theorem optimize_0plus_b_sound : forall b,
                                 beval (optimize_0plus_b b) = beval b.
Proof.  
  intros b.
  induction b; 
    try reflexivity;
    try (simpl; repeat (rewrite optimize_0plus_sound);  reflexivity).
Qed.




(**************************************************
Exercise: 4 stars, optional (optimizer)
Design exercise: The optimization implemented by our 
optimize_0plus function is only one of many imaginable 
optimizations on arithmetic and boolean expressions. 
Write a more sophisticated optimizer and prove it correct.
**************************************************)




(**************************************************
Exercise: 3 stars (bevalR)
Write a relation bevalR in the same style as aevalR, 
and prove that it is equivalent to beval.
**************************************************)

Inductive aevalR : aexp -> nat -> Prop :=
| E_ANum : forall (n : nat),
             (ANum n) || n
| E_APlus : forall (e1 e2 : aexp) (n1 n2 : nat),
              (e1 || n1) -> (e2 || n2) -> (APlus e1 e2) || (n1 + n2)
| E_AMinus : forall (e1 e2 : aexp) (n1 n2 : nat),
               (e1 || n1) -> (e2 || n2) -> (AMinus e1 e2) || (n1 - n2)
| E_AMult : forall (e1 e2 : aexp) (n1 n2 : nat),
              (e1 || n1) -> (e2 || n2) -> (AMult e1 e2) || (n1 * n2)
where " e '||' n " := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall e n,
                             (e || n) <-> aeval e = n.
Proof.
  split. 
  + intro H.
    induction H;
      simpl; try (rewrite IHaevalR1); try (rewrite IHaevalR2); reflexivity. 
  + generalize dependent n.
    induction e.
    Case "ANum".
    simpl. intros nn H. subst n. apply E_ANum.
    Case "APlus".
    simpl. intros nn H. rewrite <- H. 
    apply E_APlus.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    Case "AMinus".
    simpl. intros nn H. rewrite <- H.
    apply E_AMinus.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
    Case "AMult".
    simpl. intros nn H. rewrite <-H.
    apply E_AMult.
    apply IHe1. reflexivity.
    apply IHe2. reflexivity.
Qed.

Inductive bevalR : bexp -> bool -> Prop :=
| E_BTrue : BTrue || true
| E_BFalse : BFalse || false
| E_BNot : forall (e : bexp) (b : bool),
             (e || b) -> (BNot e) || negb b
| E_BLe : forall (e1 e2 : aexp) (n1 n2 : nat),
            (aevalR e1 n1) -> (aevalR e2 n2) -> (BLe e1 e2) || ble_nat n1 n2
| E_BEq : forall (e1 e2 : aexp) (n1 n2 : nat),
            (aevalR e1 n1) -> (aevalR e2 n2) -> (BEq e1 e2) || beq_nat n1 n2
| E_BAnd : forall (e1 e2 : bexp) (b1 b2 : bool),
             (e1 || b1) -> (e2 || b2) -> (BAnd e1 e2) || andb b1 b2
where " e '||' n " := (bevalR e n) : type_scope.

Theorem beval_iff_bevalR : forall e b,
                             (e || b) <-> beval e = b.
Proof. 
  split.
  + intro H.
    induction H; 
      simpl; 
      try (rewrite IHbevalR);
      try (rewrite IHbevalR1; rewrite IHbevalR2);
      try (apply aeval_iff_aevalR in H; apply aeval_iff_aevalR in H0; rewrite H; rewrite H0);
      try reflexivity.
  + generalize dependent b.
    induction e.
    Case "BTrue".
    intros b H. 
    destruct b.
    apply E_BTrue.
    inversion H.
    Case "BFalse".
    intros b H.
    destruct b.
    inversion H.
    apply E_BFalse.
    Case "BNot".
    intros b H.
    rewrite <- H.
    simpl. 
    apply E_BNot.
    simpl in H.
    symmetry in H.
    apply negb_sym with (b':=b) (b:=(beval e)) in H.
    rewrite H.
    apply IHe.
    apply H.
    Case "BLe".
    intros b H.
    rewrite <- H. simpl. apply E_BLe. apply aeval_iff_aevalR. reflexivity. 
    apply aeval_iff_aevalR. reflexivity.
    Case "BEq".
    intros b H.
    rewrite <- H. simpl. apply E_BEq. apply aeval_iff_aevalR. reflexivity.
    apply aeval_iff_aevalR. reflexivity.
    Case "BAnd".
    intros b H.
    rewrite <- H. simpl. apply E_BAnd. apply IHe1. reflexivity.
    apply IHe2. reflexivity.
Qed.




(**************************************************
Exercise: 1 star, optional (neq_id)
**************************************************)

Lemma neq_id : forall (T:Type) x y (p q:T), 
                 x <> y ->  (if eq_id_dec x y then p else q) = q.
Proof.
  intros T x y p q H. 
  unfold not in H.
  destruct (eq_id_dec x y).
  apply H in e. inversion e.
  reflexivity.
Qed.



(**************************************************
Exercise: 1 star (update_eq)
**************************************************)

Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (x : id) (n : nat) : state :=
  fun x' => if eq_id_dec x x' then n else st x'.

Theorem update_eq : forall n x st,
                      (update st x n) x = n.
Proof.
  intros n x st.
  unfold update.
  apply eq_id.
Qed.



(**************************************************
Exercise: 1 star (update_neq)
**************************************************)

Theorem update_neq : forall x2 x1 n st,
                       x2 <> x1 -> (update st x2 n) x1 = (st x1).
Proof.
  intros x1 x2 n st H. 
  unfold update.
  unfold not in H.
  destruct (eq_id_dec x1 x2).
  apply H in e; inversion e.
  reflexivity.
Qed.



(**************************************************
Exercise: 1 star (update_example)
Before starting to play with tactics, make sure you understand exactly what the theorem is saying!
**************************************************)

Theorem update_example : forall (n:nat),
                           (update empty_state (Id 2) n) (Id 3) = 0.
Proof.
  intros n. 
  unfold update.
  simpl. unfold empty_state.
  reflexivity.
Qed.



(**************************************************
Exercise: 1 star (update_shadow)
**************************************************)

Theorem update_shadow : forall n1 n2 x1 x2 (st : state),
                          (update (update st x2 n1) x2 n2) x1 = (update st x2 n2) x1.
Proof.
  intros n1 n2 x1 x2 st.
  unfold update.
  destruct (eq_id_dec x2 x1); reflexivity.
Qed.  



(**************************************************
Exercise: 2 stars (update_same)
**************************************************)

Theorem update_same : forall n1 x1 x2 (st : state),
                        st x1 = n1 ->
                        (update st x1 n1) x2 = st x2.
Proof.
  intros n1 x1 x2 st H.
  unfold update.
  destruct (eq_id_dec x1 x2).
  rewrite <- e. symmetry. apply H.
  reflexivity.
Qed.



(**************************************************
Exercise: 3 stars (update_permute)
**************************************************)

Theorem update_permute : forall n1 n2 x1 x2 x3 st,
                           x2 <> x1 ->
                           (update (update st x2 n1) x1 n2) x3 = (update (update st x1 n2) x2 n1) x3.
Proof.
  intros; unfold update; unfold not in H.
  destruct (eq_id_dec x1 x3).
  destruct (eq_id_dec x2 x3).
  rewrite <- e in e0.
  apply H in e0. inversion e0.
  reflexivity.
  reflexivity.
Qed.
