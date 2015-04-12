Require Export Assignment05_03.

(* problem #04: 10 points *)

Lemma imply_trans : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
intros.
apply H in H1.
apply H0 in H1.
assumption. Qed.


Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
intros. destruct H. destruct H0.
repeat (split;apply imply_trans with Q;
assumption;assumption).
Qed.


