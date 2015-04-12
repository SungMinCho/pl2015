Require Export Assignment05_12.

(* problem #13: 10 points *)



(** 2 stars, optional (beq_nat_false)  *)
Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  unfold not. induction n. destruct m. intro. inversion H.
  intros. inversion H0. destruct m. intros. inversion H0.
  intros. simpl in H. apply IHn in H. inversion H. inversion H0. reflexivity.
Qed.
(** [] *)



