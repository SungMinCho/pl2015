Require Export Assignment06_02.

(* problem #03: 10 points *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split. intro. inversion H. destruct proof. left. 
  apply ex_intro with witness. apply H0. right. apply ex_intro with witness.
  apply H0. intro. destruct H. inversion H. apply ex_intro with witness.
  left. apply proof. inversion H. apply ex_intro with witness.
  right. apply proof.
Qed.
(** [] *)


