Require Export Assignment05_18.

(* problem #19: 10 points *)




(** 2 stars (gorgeous_sum)  *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros. induction H. apply H0. rewrite <- plus_assoc. constructor. apply IHgorgeous.
  rewrite <- plus_assoc. constructor 3. apply IHgorgeous.
Qed.
(** [] *)


