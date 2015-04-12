Require Export Assignment05_04.

(* problem #05: 10 points *)


(** 1 star, optional (or_distributes_over_and)  *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
intros. split.
split. inversion H. left;assumption.
destruct H0. right. assumption.
inversion H. left. assumption.
right. destruct H0. assumption.
intro. destruct H. inversion H. left.
assumption. inversion H0. left. assumption.
right. split. assumption. assumption.
Qed.
(** [] *)


