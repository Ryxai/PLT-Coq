Require Export List.

Inductive list (X: Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check list.

Check (nil nat).

Check (cons nat 3 (nil nat)).

Check nil.

Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint repeat (X : Type) (x : X) (count : nat)
  : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
end.

Example test_repeat1 : repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

Example test_repeat2 : repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.

Fixpoint repeat' X x count : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat' X x count')
end.

Check repeat'.
Check repeat.

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 => nil _
  | S count' => cons _ x (repeat'' _ x count')
end.

Definition list123 := 
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

Fixpoint repeat''' {X: Type} (x: X) (count: nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
end.

Fixpoint app {X : Type} (l_1 l_2 : list X) : list X :=
  match l_1 with
  | nil => l_2
  | cons h t => cons h (app t l_2)
end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
end.

Example test_rev1: rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2 : rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1 : length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Fail Definition mynil := nil.

Definition mynil : list nat := nil.
Check @nil.

Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

(* Exercises poly_exercises *)

Theorem app_nil_r : forall (X : Type), forall l: list X,
  l ++ [] = l.
Proof.
  induction l as [| h l' IHl'].
  + reflexivity.
  + simpl. rewrite <- IHl' at 2. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l as [| h l' IHl'].
  + reflexivity.
  + simpl.