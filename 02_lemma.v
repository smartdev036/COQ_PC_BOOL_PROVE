Variable A B C: Prop.

Goal (A -> B -> C) -> (A ->B) -> (A -> C).

(* Save trivial_lemma. *)
intro H.
intros H' HA.
apply H.
exact HA.
apply H'.
assumption.

