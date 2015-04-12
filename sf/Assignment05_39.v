Require Export Assignment05_38.

(* problem #39: 10 points *)

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros. apply contrapositive with (ble_nat n m = true). apply le_ble_nat.
  unfold not. destruct (ble_nat n m). inversion H. intro. inversion H0.
Qed.
(** [] *)

