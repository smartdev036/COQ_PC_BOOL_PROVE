variable x: nat.
variable y: nat.

Definition add(x y:nat) : nat := x+y.

Eval compute in add 3 4.