Add LoadPath "C:\Users\Jonathan\source\repos\PLT-Coq\Software Foundations\Logical Foundations".
Require Export Lists.


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
  + simpl. rewrite IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  induction l as [| h l' IHl'].
  + reflexivity.
  + intros. simpl. rewrite <- IHl'. reflexivity.
Qed.

Lemma app_length : forall (X: Type) (l_1 l_2 : list X),
  length (l_1 ++ l_2) = length l_1 + length l_2.
Proof.
  induction l_1 as [| h l_1' IHl1'].
  - reflexivity.
  - intros. simpl. rewrite -> IHl1'. reflexivity.
Qed.

(* Exercises more_poly exercises *)

Theorem rev_app_distr : forall X (l_1 l_2 : list X),
  rev (l_1 ++ l_2) = rev l_2 ++ rev l_1.
Proof.
  intros. induction l_1 as [| h l_1' IHl1'].
  - rewrite app_nil_r. reflexivity.
  - simpl. rewrite IHl1'. rewrite app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall X: Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros. induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. rewrite -> IHl'. reflexivity.
Qed.

(* Polymorphic pairs *)

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, s) => x
end.

Definition snd {X Y : Type} (p: X * Y) : Y :=
  match p with  
  | (x, y) => y
end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
  : list (X * Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x,y) :: (combine tx ty)
end.

(* Exercise combine_checks *)

Check @combine.
Compute (combine [1;2] [false;false;true;true]).

(* Exercise split *)

Fixpoint split {X Y : Type} (l : list (X*Y))
  : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split t with
      | (xs, ys) => (x::xs, y::ys)
    end
end.

Example test_split:
  split [(1, false);(2, false)] = ([1;2], [false;false]).
Proof. reflexivity. Qed.

Module OptionPlayground.

Inductive option (X: Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O 
                then Some a 
                else nth_error l' (pred n)
end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.

Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.

Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(* Exercise hd_error_poly *)

Definition hd_error {X : Type} (l : list X) 
  : option X :=
    match l with
    | [] => None
    | h :: t => Some h
end.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

(* Functions as Data *)

Definition doit3times {X: Type} (f: X -> X) (n : X) : X :=
f (f (f (n))).

Check @doit3times.

Example test_doit3times : doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t) else filter test t
end.

Example test_filter1 : filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool := beq_nat (length l) 1.

Example test_filter2: filter length_is_1 [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers'2: countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_anon_fun': doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2':  filter (fun l => beq_nat (length l) 1) 
  [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof. reflexivity. Qed.

(* Exercise filter_even_gt7 *)
Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n => (andb (evenb n) (negb (blt_nat n 7)))) l.

Example test_filter_even_gt7_1 : filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_event_gt7_2 : filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

(* Exercise partition *)
Definition partition {X : Type} (test : X -> bool) (l : list X) : list X * list X :=
  ((filter test l), (filter (fun n => (negb (test n))) l)).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.

Example test_partition2 : partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y : Type} (f: X -> Y) (l : list X) : (list Y) :=
  match l with 
  | [] => []
  | h :: t => (f h) :: (map f t)
end.

Example test_map1 : map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Example test_map2 : map oddb [2;1;2;5] = [false; true; false; true].
Proof. reflexivity. Qed.

Example test_map3 : map (fun n => [evenb n; oddb n]) [2;1;2;5] = 
  [[true; false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* Exercise map_rev *)

Lemma map_app_distr : forall (X Y: Type) (f : X -> Y) (l_1 l_2 : list X),
  map f (l_1 ++ l_2) = (map f l_1) ++ (map f l_2).
Proof.
  intros.
  induction l_1 as [| h_1 l_1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros. induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. rewrite -> map_app_distr. rewrite IHl'. reflexivity.
Qed.

(* Exercise flat_map *)

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | h :: t => f h ++ (flat_map f t)
end.

Example test_flat_map1: flat_map (fun n => [n; n; n]) [1;5;4] =
  [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) : option Y :=
  match xo with
  | None => None
  | Some x => Some (f x)
end.

Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with 
  | nil => b
  | h :: t => f h (fold f t b)
end.

Check (fold andb).

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2: fold andb [true; true; false; true] true = false.
Proof. reflexivity. Qed.

Example fold_example3: fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(* Exercise fold_length *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros. induction l as [| h l' IHl'].
  - reflexivity.
  - simpl.
    rewrite <- IHl'.
    unfold fold_length.
    reflexivity.
Qed.

(* Exercise fold_map *)

Definition fold_map {X Y: Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun h t => (f h) :: t) l [].

Example test_fold_map : fold_map (fun x => x) [1;2;3;4] = [1;2;3;4].
Proof. reflexivity. Qed.

Theorem fold_map_correct : forall (X Y: Type) (f : X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros. induction l as [| h l' IHl'].
  - reflexivity.
  - simpl. 
    rewrite <- IHl'.
    unfold fold_map.
    reflexivity.
Qed.


(* Exercise currying *)

Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X) (y : Y) : Z := f(x, y).

Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y, 
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros.
  unfold prod_curry.
  unfold prod_uncurry.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p  = f p.
Proof.
  intros.
  destruct p.
  unfold prod_uncurry.
  simpl.
  unfold prod_curry.
  reflexivity.
Qed.

(* Exercise church_numerals *)

Module Church.

Definition nat := forall X : Type, (X -> X) -> X -> X.

Definition one : nat := fun (X : Type) (f : X -> X) (x : X) => f x.

Definition two : nat := fun (X : Type) (f : X -> X) (x : X) => f (f x).

Definition zero : nat := fun (X : Type) (f : X -> X) (x : X) => x.

Definition three : nat := @doit3times.

Definition succ (n : nat) : nat := 
  fun (X : Type) (f : X -> X) (x : X) => f ((n X f) x).

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

Definition plus (n m : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => m X f ((n X f) x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 : plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

Definition mult (n m : nat) : nat :=  
  fun (X : Type) (f : X -> X) (x : X) => (n X (m X f) x).

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

Definition exp (n m  : nat) : nat :=
  fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f) x.

Example exp_1 : exp two two = plus two two .
Proof. reflexivity. Qed.

Example exp_2 : exp three two = plus (mult two (mult two two )) one.
Proof. reflexivity. Qed.

Example exp_3 : exp three zero = one.
Proof. reflexivity. Qed.

End Church.



