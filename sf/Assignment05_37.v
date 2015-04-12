Require Export Assignment05_36.

(* problem #37: 10 points *)

Theorem le_ble_nat : forall n m,
  n <= m ->
  ble_nat n m = true.
Proof.
  induction n. intros. reflexivity.
  intros. destruct m. inversion H. apply Sn_le_Sm__n_le_m in H.
  apply IHn in H. apply H.
Qed.

