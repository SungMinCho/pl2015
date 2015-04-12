Require Export Assignment05_25.

(* problem #26: 10 points *)











(** 3 star (even__ev)  
    Note that proving [even__ev] directly is hard.
    You might find it easier to prove [even__ev_strong] first
    and then prove [even__ev] using it.
*)

Lemma even__ev_strong: forall n : nat, 
  (even (pred n) -> ev (pred n)) /\ (even n -> ev n).
Proof.
  intros. induction n. repeat split;constructor.
  simpl. split. destruct IHn. apply H0. intro. destruct n.
  inversion H. constructor. unfold even in H. simpl in H.
  destruct IHn. apply H0 in H. apply H.
Qed.
(** [] *)


