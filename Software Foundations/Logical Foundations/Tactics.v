Set Warnings "-notation-overridden,-parsing".
Add LoadPath "C:\Users\Jonathan\source\repos\PLT-Coq\Software Foundations\Logical Foundations".
Require Export Polymorphic Lists.

Theorem silly1 : forall (n m o p: nat),
  n = m ->
  [n;o] = [n;p] ->
  [n;o] = [m;p].
Proof. 
  intros n m o p eq_1 eq_2.
  rewrite <- eq_1.
  apply eq_2.
Qed.


Theorem silly2: forall (n m o p : nat),
  n = m ->
  (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
  [n;o] = [m; p].
Proof.
  intros n m o p eq_1 eq_2.
  apply eq_2.
  apply eq_1.
Qed.


Theorem silly2a : forall (n m : nat),
  (n, n) = (m, m) ->
  (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq_1 eq_2.
  apply eq_2.
  apply eq_1.
Qed.

(* Exercise silly_ex *)

Theorem silly_ex : 
  (forall n, evenb n = true -> oddb (S n) = true) ->
  oddb 3 = true -> 
  evenb 4 = true.
Proof.
  intros eq_1 eq_2.
  apply eq_2.
Qed.

Theorem silly3_firsttry : forall (n : nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

(* Exercise apply_exercise1 *)

Theorem rev_exercise1 : forall  (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed.

(* Apply with tactic *)

Example trans_eq_example : forall (a b c d e f : nat),
  [a;b] = [c;d] -> 
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq_1 eq_2.
  rewrite eq_1. rewrite eq_2.
  reflexivity.
Qed.

Theorem trans_eq: forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq_1 eq_2.
  rewrite eq_1.
  rewrite eq_2.
  reflexivity.
Qed.

Theorem trans_eq_example': forall (a b c d e f : nat),
  [a;b] = [c;d] ->
  [c;d] = [e;f] ->
  [a;b] = [e;f].
Proof.
  intros a b c d e f eq_1 eq_2.
  apply trans_eq with (m := [c;d]).
  apply eq_1.
  apply eq_2.
Qed.

(* Exercise apply_with_exercise *)
Example trans_eq_exercise : forall (n m o p: nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq_1 eq_2.
  apply trans_eq with (m := m).
  apply eq_2.
  apply eq_1.
Qed.

(* Inversion tactic *)

Theorem S_injective : forall (n m : nat),
  S n = S m -> 
  n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex_1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex_2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  inversion H as [Hnm].
  reflexivity.
Qed.

(* Exercise inversion_ex_3 *)

Example inversion_ex_3 : forall (X : Type) (x y z w : X) (l j : list X),
  x :: y :: l = w :: z :: j ->
  x :: l = z :: j ->
  x = y.
Proof.
  intros X x y z w l j H_1 H_2.
  inversion H_2.
  inversion H_1.
  reflexivity.
Qed.

Theorem beq_nat_0_1 : forall n,
  beq_nat 0 n = true -> n = 0.
  intros n.
  destruct n as [| n'].
  - intros H.
    reflexivity.
  - intros H. 
    inversion H.
Qed.

Theorem inversion_ex_4 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

(* Exercise inversion_ex_6 *)

Example inversion_ex_6 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros X x y z l j H0 H1.
  inversion H1.
  inversion H0.
Qed.

Theorem f_equal : forall (A B : Type) (f : A -> B) (x y : A),
  x = y -> f x = f y.
Proof. 
  intros A B f x y eq.
  rewrite eq.
  reflexivity.
Qed.

(* Using tactics on hypothesis *)

Theorem S_inj : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof. 
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 -> 
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

(* Exercise plus_n_n_injective *)


Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [| n'].
  - intros m.
    destruct m as [| m'].
    + reflexivity.
    + intros H.
      inversion H.
  - intros m H.
    rewrite <- plus_n_Sm in H.
    simpl in H.
    destruct m as [| m'].
    + inversion H.
    + rewrite <- plus_n_Sm in H.
      simpl in H.
      apply S_injective in H.
      apply S_injective in H.
      apply IHn' in H.
      rewrite H.
      reflexivity.
Qed.

(* Varying the induction hypothesis *)

Theorem double_injective_FAILED : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m. 
  induction n as [| n'].
  - simpl. 
    intros eq.
    destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - intros eq. destruct m as [| m'].
    + inversion eq.
    + apply f_equal.
Abort.


Theorem double_injective: forall n m, 
  double n = double m -> n = m.
Proof. 
  intros n.
  induction n as [| n'].
  - simpl.
    intros m eq.
    destruct m as [| m'].
    + reflexivity.
    + inversion eq.
  - simpl.
    intros m eq.
    destruct m as [| m'].
    + simpl.
      inversion eq.
    + apply f_equal.
      apply IHn'.
      inversion eq.
      reflexivity.
Qed.

(* Exercise beq_nat_true *)

Theorem beq_nat_true : forall n m,
  beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n as [| n'].
  + intros m H.
    destruct m as [| m'].
    - reflexivity.  
    - inversion H.
  + intros m H.
    destruct m as [| m'].
    - inversion H.
    - apply f_equal.
      apply IHn'.
      inversion H.
      reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [| m'].
  - simpl. intros n eq . destruct n as [| n'].
     + reflexivity.
     + inversion eq.
  - intros n eq. destruct n as [| n'].
    + inversion eq.
    + apply f_equal.
      apply IHm'.
      inversion eq.
      reflexivity.
Qed.

Search NatList.beq_id.

Theorem beq_id_true : forall x y,
 NatList.beq_id x y = true -> x = y.
Proof.
  

