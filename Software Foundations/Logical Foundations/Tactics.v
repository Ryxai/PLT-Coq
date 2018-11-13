Set Warnings "-notation-overridden,-parsing".

Require Export Polymorphic.

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