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


  
  