Require Export Assignment05_14.

(* problem #15: 10 points *)



(** 1 star (double_even)  *)
Theorem double_even : forall n,
  ev (double n).
Proof.
  induction n. constructor. simpl. constructor 2. apply IHn.
Qed.
(** [] *)




