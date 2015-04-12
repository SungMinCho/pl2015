Require Export Assignment05_30.

(* problem #31: 10 points *)

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  intros. induction H. constructor. constructor. apply IHle.
Qed.

