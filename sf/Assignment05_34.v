Require Export Assignment05_33.

(* problem #34: 10 points *)

Lemma Sn_le_m__n_le_m :
forall n m , S n <= m -> n <= m.
Proof.
  intros. apply le_trans with (S n). constructor. constructor.
  apply H. 
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  unfold lt. 
  intros. destruct m.
  inversion H. apply Sn_le_Sm__n_le_m in H. split.
  apply n_le_m__Sn_le_Sm. induction n2.
  rewrite plus_O in H. apply H. rewrite plus_n_Sm in H.
  apply Sn_le_m__n_le_m in H. apply IHn2 in H. apply H.
  apply n_le_m__Sn_le_Sm. induction n1. apply H. simpl in H.
  apply Sn_le_m__n_le_m in H. apply IHn1 in H. apply H.
Qed.

