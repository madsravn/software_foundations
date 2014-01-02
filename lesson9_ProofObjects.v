(* Proof Objects *)
Require Export Logic.

Inductive beautiful : nat -> Prop :=
  b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall n m : nat, beautiful n -> beautiful m -> beautiful (n + m).


Print beautiful.

Check (b_sum 3 5 b_3 b_5).

Theorem eight_is_beautiful : beautiful 8.
Proof. 
  apply (b_sum 3 5 b_3 b_5).
Qed.

Theorem eight_is_beautiful'' : beautiful 8.
Proof. 
  Show Proof.
  apply b_sum with (n:=3) (m:=5).
  Show Proof.
  apply b_3.
  Show Proof.
  apply b_5.
  Show Proof.
Qed.

Definition eight_is_beautiful''' : beautiful 8 :=
  b_sum 3 5 b_3 b_5.

Print eight_is_beautiful.
Print eight_is_beautiful''.
Print eight_is_beautiful'''.

(**************************************************
Exercise: 1 star (six_is_beautiful)
Give a tactic proof and a proof object showing that 6 is beautiful.
**************************************************)

Theorem six_is_beautiful :
  beautiful 6.
Proof.
  apply b_sum with (n:=3) (m:=3).
  apply b_3. apply b_3.
Qed.

Definition six_is_beautiful' : beautiful 6 :=
  b_sum 3 3 b_3 b_3.



(**************************************************
Exercise: 1 star (nine_is_beautiful)
Give a tactic proof and a proof object showing that 9 is beautiful.
**************************************************)

Theorem nine_is_beautiful : beautiful 9.
Proof.
  


Definition nine_is_beautiful' : beautiful 9 :=
  (* FILL IN HERE *) admit.
☐
