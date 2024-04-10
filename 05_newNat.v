(* Define the newNat data type and conversion functions *) 

Inductive newNat : Type :=
|NewO : newNat 
|NewS : newNat -> newNat.

Fixpoint convert (n: nat) :newNat := 
  match n with 
  | O => NewO 
  | S n' => NewS (convert n') 
  end.

Fixpoint unconvert(n: newNat ) : nat := 
  match n with 
  | NewO => O 
  | NewS n' => S (unconvert n')
  end.

Compute convert 3.
Compute  unconvert (NewS (NewS (NewS NewO))).
Compute  (S (S (S O))).

(* Use the conversion functions *) 
Example ex1 : convert 3 = NewS (NewS (NewS NewO)).
Proof. reflexivity. Qed.

Example ex2 : unconvert (NewS (NewS (NewS NewO))) =3.
Proof. reflexivity. Qed.
