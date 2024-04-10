Section Declaration.

Variable n : nat.
Hypothesis Pos_n:(gt n 0).

Check (forall m:nat, gt m 0).

Check gt.

Check gt n 0.
Reset Declaration.

Check S.

Definition one := (S 0).
Definition two := (S one).
Definition three : nat := (S two).

Definition double (m: nat) := plus m m.

Variables A B C: Prop.

Goal (A -> B -> C) -> (A -> B) -> (A -> C ).

intro H.    
(* intros H1 H2 H3. *)

intros H' HA.

apply H.
exact HA.
assumption.


