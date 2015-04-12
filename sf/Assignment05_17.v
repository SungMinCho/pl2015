Require Export Assignment05_16.

(* problem #17: 10 points *)





(** 3 stars (b_timesm)  *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  induction m. intro. simpl. constructor.
  intro. simpl. constructor. apply H. apply IHm in H. apply H.
Qed.
(** [] *)




