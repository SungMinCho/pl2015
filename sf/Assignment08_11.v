Require Export Assignment08_10.

(* problem #11: 10 points *)

(** **** Exercise: 2 stars (assign_aequiv)  *)
Theorem assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).
Proof.
  intros.
  assert (forall st, st = update st X (aeval st e)). intros. apply functional_extensionality.
  intros. unfold update. destruct (eq_id_dec X x); try reflexivity. unfold aequiv in H.
  assert (HH := H st). simpl in HH. subst. apply HH.
  split; intros. inversion H1; subst. rewrite H0. apply E_Ass. reflexivity.
  inversion H1; subst. rewrite <- H0. apply E_Skip.
Qed.

(*-- Check --*)
Check assign_aequiv : forall X e,
  aequiv (AId X) e -> 
  cequiv SKIP (X ::= e).

