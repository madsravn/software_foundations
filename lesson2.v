Require Export Basics.

Module NatList.

Inductive natprod : Type :=
pair : nat -> nat -> natprod.

Eval simpl in (pair 3 5).

Definition fst (p : natprod) : nat :=
match p with 
| pair x y => x
end.

Definition snd (p : natprod) : nat :=
match p with 
| pair x y => y
end.

Eval simpl in (fst (pair 3 5)).

Notation "( x , y )" := (pair x y).

Definition swap_pair (p : natprod) : natprod :=
match p with
| (x,y) => (y, x)
end.

Theorem surjective_pairing' : forall (n m : nat),
(n, m) = (fst (n,m), snd (n, m)).
Proof.
(* simpl. *)
reflexivity.
Qed.

Theorem surjective_pairing_stuck : forall (p: natprod),
p = (fst p, snd p).
Proof.
simpl.
Admitted.

Theorem surjective_pairing : forall (p: natprod),
p = (fst p, snd p).
Proof.
intros p. 
destruct p as (n,m).
reflexivity.
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
(snd p, fst p) = swap_pair p.
Proof.
intros p.
destruct p as (m,n).
reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
fst (swap_pair p) = snd p.
Proof.
intros p.
destruct p as (m,n).
simpl.
reflexivity.
Qed.

Inductive natlist : Type :=
| nil : natlist
| cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 ( cons 3 nil)).

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "x + y" := (plus x y) (at level 50, left associativity).

Fixpoint repeat (n count : nat) : natlist :=
match count with 
| O => nil
| S count' => n :: (repeat n count')
end.

Fixpoint length (l : natlist) : nat :=
match l with
| nil => O
| h :: t => S (length t)
end.

Fixpoint app (l1 l2 : natlist) : natlist :=
match l1 with 
| nil => l2
| h :: t => h :: (app t l2)
end.

Notation "x ++ y" := (app x y) (right associativity, at level 60).

Example test_app1 : [1,2,3] ++ [4,5,6] = [1,2,3,4,5,6].
Proof. reflexivity. Qed.

Example test_app2 : nil ++ [4,5] = [4,5].
Proof. reflexivity. Qed.

Example test_app3 : [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
match l with
| nil => default
| h :: t => h
end.

Definition tail (l : natlist) : natlist :=
match l with
| nil => nil
| h :: t => t
end.

Example test_hd1 : hd 0 [1,2,3] = 1.
Proof. reflexivity. Qed.
Example test_hd2 : hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tail : tail [1,2,3] = [2,3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
match l with
| nil => nil
| O :: t => nonzeros t
| h :: t => h :: nonzeros t
end.

Example nzex1 : nonzeros (1::0::2::0::[]) = 1::2::[].
Proof. reflexivity. Qed.
Example test_nonzeros: nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. reflexivity. Qed.

Fixpoint evenp (n : nat) : bool :=
match n with
| O => true
| S O => false
| S (S n') => evenp n'
end.

Example test_even : evenp 3 = false.
Proof. reflexivity. Qed.
Example test_even2 : evenp 4 = true.
Proof. simpl. reflexivity. Qed. 

Fixpoint oddmembers (l : natlist) : natlist :=
match l with
| nil => nil
| h :: t => match evenp h with
            | true => oddmembers t
            | false => h :: oddmembers t
            end
end.

Example test_oddmembers: oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. simpl. reflexivity. Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
match l with
| nil => O
| h :: t => match evenp h with
            | true => countoddmembers t
            | false => S (countoddmembers t)
            end
end.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. simpl. reflexivity. Qed.
Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
Proof. reflexivity. Qed. 
Example test_countoddmembers3: countoddmembers nil = 0.
Proof. reflexivity. Qed.

Inductive natlistprod : Type :=
lpair : natlist -> natlist -> natlistprod.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
match lpair l1 l2 with
| lpair nil nil => nil
| lpair nil l => l
| lpair l nil => l
| lpair (h1 :: t1) (h2 :: t2) => h1 :: h2 :: (alternate t1 t2)
end.

Example test_alternate1: alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. simpl. reflexivity. Qed.

Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. reflexivity. Qed. 
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof. simpl. reflexivity. Qed. 
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof. reflexivity. Qed. 

Definition bag := natlist.

Fixpoint eq (a b : nat) :=
match (a, b) with
| (O, O) => true
| (O, _) | (_, O) => false
| (S n, S m) => eq n m
end.

Fixpoint count (v : nat) (s : bag) : nat :=
match s with 
| nil => 0
| h :: t => match eq v h with
            | true => S (count v t)
            | false => count v t
            end
end.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. reflexivity. Qed. 
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. reflexivity. Qed. 

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. reflexivity. Qed. 

Definition add (v : nat) (s : bag) : bag := v :: s.

Example test_add1: count 1 (add 1 [1,4,1]) = 3.
Proof. reflexivity. Qed.

Example test_add2: count 5 (add 1 [1,4,1]) = 0.
Proof. reflexivity. Qed. 

Fixpoint geq (n : nat) (m : nat) :=
match (n, m) with
| (O,O) | (_, O) => true
| (O, _) => false
| (S nn, S mm) => geq nn mm
end.

Definition member (v:nat) (s:bag) : bool := geq (count v s) 1.

Example test_member1: member 1 [1,4,1] = true.
Proof. reflexivity. Qed. 
Example test_member2: member 2 [1,4,1] = false.
Proof. reflexivity. Qed. 

Fixpoint remove_one (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| h :: t => match eq h v with
            | true => t
            | false => h :: remove_one v t
            end
end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. reflexivity. Qed. 
Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0. Proof. reflexivity. Qed. 
Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2. Proof. reflexivity. Qed. 
Example test_remove_one4: 
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1. Proof. reflexivity. Qed. 

Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with
| nil => nil
| h :: t => match eq v h with
            | true => remove_all v t
            | false => h :: remove_all v t
            end
end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0. Proof. reflexivity. Qed. 
Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0. Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2. Proof. reflexivity. Qed. 
Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0. Proof. reflexivity. Qed. 

Check andb true true.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
match s1 with 
| nil => true
| h :: t => andb (member h s2) (subset t (remove_one h s2))
end.

Example test_subset1: subset [1,2] [2,1,4,1] = true. Proof. reflexivity. Qed. 
Example test_subset2: subset [1,2,2] [2,1,4,1] = false. Proof. simpl. reflexivity. Qed. 

Theorem nil_app : forall l : natlist,
[] ++ l = l.
Proof. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
 length (l1 ++ l2) = (length l1) + (length l2).
Proof. intros l1 l2.
induction l1 as [| n l1'].
simpl. reflexivity. 
simpl. rewrite -> IHl1'. reflexivity. 
Qed. 

Fixpoint snoc (l : natlist) (v : nat) : natlist :=
match l with
| nil => [v]
| h :: t => h :: (snoc t v)
end. 

Fixpoint rev (l : natlist) : natlist :=
match l with
| nil => nil
| h :: t => snoc (rev t) h
end.

Example test_rev1 : rev [1,2,3] = [3,2,1]. Proof. reflexivity. Qed.
Example test_rev2 : rev nil = nil. Proof. reflexivity. Qed. 

Theorem rev_length_firsttry : forall l : natlist,
length (rev l) = length l.
Proof.
intros l. induction l as [| n l']. 
reflexivity. 
simpl. rewrite <- IHl'. 
Theorem length_snoc : forall n : nat, forall l : natlist,
length (snoc l n) = S (length l).
Proof. intros n l. induction l as [| nn l]. simpl. reflexivity. 
simpl. rewrite -> IHl. reflexivity. Qed.
rewrite -> IHl'. rewrite -> length_snoc. rewrite -> IHl'. reflexivity. Qed.  

SearchAbout rev.

(* Exercise: 3 stars, recommended (list_exercises) *)
(* More practice with lists. *)

Theorem app_nil_end : forall l : natlist, 
  l ++ [] = l.
Proof. intros l. induction l as [| n ll]. reflexivity. 
simpl. rewrite -> IHll. reflexivity. Qed.  
  
Theorem cibele : forall (l : natlist) (n : nat),
 rev(snoc l n) = n :: (rev l).
Proof.
 intros l n.  
 induction l as [| h t].
 simpl. reflexivity. 
 simpl. rewrite -> IHt. simpl. reflexivity. 
Qed. 

Theorem rev_involutive :  forall l : natlist,
  rev (rev l) = l.
Proof.
 intro l.
 induction l as [| h t].
 reflexivity. 
 simpl. rewrite -> cibele. rewrite -> IHt. reflexivity. 
Qed. 

(* There is a short solution to the next exercise. 
If you find yourself getting tangled up, step back and try to look for a simpler way. *)

Theorem app_ass4 :  forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  Theorem app_right : forall l1 l2 l3 : natlist,
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
  Proof. 
    intros l1 l2 l3.
    induction l1 as [|h1 t1]. reflexivity. 
    simpl. rewrite -> IHt1. reflexivity.
  Qed. 
  rewrite <- app_right. rewrite app_right. reflexivity.
Qed.   


Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
 intros l n. induction l as [| nn ll]. reflexivity. 
 simpl. rewrite <- IHll. reflexivity. 
Qed. 

Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof. 
  intros l1 l2.
  induction l1 as [| h1 t1].
  simpl. rewrite -> app_nil_end. reflexivity. 
  simpl. rewrite -> snoc_append. rewrite -> IHt1. rewrite -> snoc_append. rewrite -> app_right. reflexivity. 
Qed. 
  

(* An exercise about your implementation of nonzeros: *)

Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
Admitted.   
(* OPTIONS *)
 
Inductive natoption : Type :=
| Some : nat -> natoption
| None : natoption.

Fixpoint beq_nat (n : nat) (m : nat) : bool :=
match (n, m) with
| (O, O) => true
| (_, O) | (O, _) => false
| (S nn, S mm) => beq_nat nn mm
end.

Fixpoint index (n : nat) (l : natlist) : natoption :=
match l with
| nil => None
| a :: ll => match beq_nat n 0 with
	     | true => Some a
	     | false => index (pred n) ll
	     end
end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4,5,6,7] = Some 7.
Proof. simpl. reflexivity. Qed. 
Example test_index3 : index 10 [4,5,6,7] = None.
Proof. reflexivity. Qed. 

Fixpoint index' (n : nat) (l : natlist) : natoption :=
match l with
| nil => None
| a::ll => if beq_nat n 0
           then Some a
           else index' (pred n) ll
end.

Definition option_elim (d : nat) (o : natoption) : nat :=
match o with
| Some nn => nn
| None => d
end.

Definition hd_opt (l : natlist) : natoption :=
match l with
| nil => None
| h::t => Some h
end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3 : hd_opt [5,6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l : natlist) (default : nat),
hd default l = option_elim default (hd_opt l).
Proof. 
  intros l n.
  destruct l as [| h t].
  reflexivity.
  reflexivity.
Qed.

Inductive nopt_pair : Type :=
| Nop : natoption -> natoption -> nopt_pair.

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
match l1 with
| nil => match l2 with
         | nil => true
         | _ => false
         end
| h1::t1 => match l2 with
            | nil => false
            | h2::t2 => if beq_nat h1 h2 
                        then beq_natlist t1 t2
                        else false
            end
end.
Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1,2,3] [1,2,3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1,2,3] [1,2,4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall l : natlist,
true = beq_natlist l l.
Proof. 
 intro l. induction l as [| h t].
 simpl. reflexivity. 
 simpl. rewrite <- IHt. assert (H : beq_nat h h = true).
 induction h as [| hh]. 
 simpl. reflexivity. 
 simpl. rewrite -> IHhh. 
 reflexivity. 
 rewrite -> H. 
 reflexivity. 
Qed.

Module Dictionary.

Inductive dictionary : Type :=
| empty : dictionary
| record : nat -> nat -> dictionary -> dictionary. 

Definition insert (key value : nat) (d : dictionary) :=
 (record key value d).

Fixpoint find (key : nat) (d : dictionary) : natoption :=
 match d with
 | empty => None
 | record k v d' => if (beq_nat key k)
                    then (Some v) 
                    else (find key d')
 end.

Theorem dictionary_invariant1 : forall (d : dictionary) (k v : nat),
  (find k (insert k v d)) = Some v.
Proof. 
 intros d k v. 
 simpl. assert (H : beq_nat k k = true).  
  induction k as [| kk]. 
  reflexivity. 
  simpl. rewrite -> IHkk. reflexivity. 
  rewrite -> H. reflexivity. 
Qed. 

Theorem dictionary_invariant2 : forall (d : dictionary) (m n o : nat),
(beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
Proof. 
 intros d m n o.
 intro H. 
 simpl. rewrite -> H. reflexivity. 
Qed. 

End Dictionary.

End NatList.