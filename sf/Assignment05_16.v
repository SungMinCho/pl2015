Require Export Assignment05_15.

(* problem #16: 10 points *)







(** 2 stars (b_times2)  *)
Theorem b_times2: forall n, beautiful n -> beautiful (2*n).
Proof.
  simpl. intros. assert (forall n, n + 0 = n). induction n0. reflexivity.
  simpl. rewrite IHn0. reflexivity. rewrite H0. constructor. apply H. apply H.
Qed.
(** [] *)



