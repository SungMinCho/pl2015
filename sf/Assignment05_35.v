Require Export Assignment05_34.

(* problem #35: 10 points *)

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply Sn_le_m__n_le_m in H.
  apply n_le_m__Sn_le_Sm. apply H.
Qed.

