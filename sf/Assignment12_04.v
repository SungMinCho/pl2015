Require Export Assignment12_03.

(* problem #04: 10 points *)

Corollary soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').
Proof.
  unfold not. unfold stuck. unfold not. intros.
  destruct H1.
  unfold normal_form in H1.
  unfold not in H1.
  induction H0.
  apply progress in H.
  inversion H. apply H2 in H0;auto. apply H1 in H0;auto.
  eapply preservation in H; (try apply H0).
  apply IHmulti in H; try assumption.
Qed.

(*-- Check --*)
Check soundness : forall t t' T,
  empty |- t \in T -> 
  t ==>* t' ->
  ~(stuck t').

