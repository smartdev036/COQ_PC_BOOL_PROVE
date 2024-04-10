Variable A B C : Prop.

Lemma distr_impl : (A ->B -> C) -> (A -> B) -> (A->C).
intros.

apply H.
assumption.
apply H0.
assumption.

apply H; [ assumption | apply H0; assumption ].


Save sss.