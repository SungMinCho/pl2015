Require Export Assignment05_29.

(* problem #30: 10 points *)

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  induction n. constructor. constructor. apply IHn.
Qed.

