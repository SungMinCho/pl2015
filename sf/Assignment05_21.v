Require Export Assignment05_20.

(* problem #21: 10 points *)





(** 2 stars (ev_sum)  *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros. induction H. apply H0.
  simpl. constructor. apply IHev.
Qed.
(** [] *)





