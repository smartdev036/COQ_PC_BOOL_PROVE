(* Define the nat type *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(* Define the add function using recursion *)
Fixpoint add (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(* Define some test cases *)
Definition test1 := add (S (S O)) (S (S (S O))).
Definition test2 := add O (S (S (S (S O)))).
Definition test3 := add (S (S (S O))) O.
Definition test4 := add O O.

(* Evaluate the test cases using Compute *)
Compute test1.
Compute test2.
Compute test3.
Compute test4.