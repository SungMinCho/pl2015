Require Export Assignment05_10.

(* problem #11: 10 points *)


(** 3 stars (excluded_middle_irrefutable)  *)
(** This theorem implies that it is always safe to add a decidability
axiom (i.e. an instance of excluded middle) for any _particular_ Prop [P].
Why? Because we cannot prove the negation of such an axiom; if we could,
we would have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Lemma not_distr_or : forall P Q, ~(P \/ Q) -> (~P /\ ~Q).
Proof.
  intros. unfold not in *. split. intro. assert (P \/ Q). left. assumption.
  apply H in H1. inversion H1. intro. assert (P \/ Q). right. assumption.
  apply H in H1. inversion H1. 
Qed.

Theorem excluded_middle_irrefutable:  forall (P:Prop), ~ ~ (P \/ ~ P).  
Proof.
  intros. unfold not. intro. apply not_distr_or in H. destruct H. unfold not in *.
  apply H0 in H. inversion H.
Qed.
