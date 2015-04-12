Require Export Assignment05_11.

(* problem #12: 10 points *)




(** 2 stars (false_beq_nat)  *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof.
  unfold not.
  induction n. destruct m. intro. assert (0=0). reflexivity.
  apply H in H0. inversion H0. reflexivity.
  destruct m. reflexivity. simpl. intro.
  assert (n = m -> False). intro. assert (S n = S m). rewrite H0. reflexivity.
  apply H in H1. inversion H1. apply IHn in H0. apply H0.
Qed.
(** [] *)




