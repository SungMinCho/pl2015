Require Export Assignment05_08.

(* problem #09: 10 points *)



(** 2 stars (contrapositive)  *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
intros. unfold not in *. intro.
apply H in H1. apply H0 in H1. apply H1.
Qed.
(** [] *)



