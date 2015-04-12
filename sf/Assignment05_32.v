Require Export Assignment05_31.

(* problem #32: 10 points *)

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros. inversion H. constructor. clear H1 H0 n0 m0.
  assert (n <= S n). constructor. constructor. apply le_trans with (S n).
  apply H0. apply H2.
Qed.

