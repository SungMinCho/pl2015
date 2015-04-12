Require Export Assignment05_09.

(* problem #10: 10 points *)




(** 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
intros. unfold not. intro.
destruct H. apply H0 in H. apply H.
Qed.
(** [] *)



