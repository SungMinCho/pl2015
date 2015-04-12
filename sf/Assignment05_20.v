Require Export Assignment05_19.

(* problem #20: 10 points *)








(** 3 stars, advanced (beautiful__gorgeous)  *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros. induction H. constructor. constructor. constructor. constructor 3. constructor.
  apply gorgeous_sum. assumption. assumption.
Qed.
(** [] *)




