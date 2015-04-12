Require Export Assignment05_35.

(* problem #36: 10 points *)

Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  induction n. intros. apply O_le_n.
  intros. destruct m. inversion H. simpl in H.
  apply IHn in H. apply n_le_m__Sn_le_Sm. apply H.
Qed.

