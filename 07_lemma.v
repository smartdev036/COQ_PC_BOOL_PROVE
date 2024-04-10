From Coq Require Import Arith.

Lemma my_lemma : forall x : nat, x+1 = 1+x.
Proof.
  intros x.
  rewrite Nat.add_comm.
  reflexivity.
Qed.



