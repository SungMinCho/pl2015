Require Export Assignment05_32.

(* problem #33: 10 points *)

Lemma plus_O : forall a, a + 0 = a.
Proof. induction a. reflexivity. simpl. rewrite IHa. reflexivity. Qed.

Lemma plus_n_Sm : forall n m, n + (S m) = S (n + m).
Proof. induction n. reflexivity. simpl. intro. rewrite IHn.
reflexivity. Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  induction b. rewrite plus_O. constructor. rewrite plus_n_Sm. constructor.
  apply IHb.
Qed.

