Require Export Assignment08_06.

(* problem #07: 10 points *)

(** **** Exercise: 2 stars (IFB_false)  *)
Theorem IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.
Proof.
  unfold cequiv. split.
  intros. inversion H0; subst. unfold bequiv in H. simpl in H. assert (HH := H st).
  rewrite HH in H6. inversion H6. assumption.
  intros. apply E_IfFalse. unfold bequiv in H. assert (HH := H st). apply HH. assumption.
Qed.

(*-- Check --*)
Check IFB_false: forall b c1 c2,
  bequiv b BFalse  ->
  cequiv 
    (IFB b THEN c1 ELSE c2 FI) 
    c2.

