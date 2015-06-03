Require Export Assignment10_10.

(* problem #11: 10 points *)

(** **** Exercise: 3 stars, optional (interp_tm)  *)
(** Remember that we also defined big-step evaluation of [tm]s as a
    function [evalF].  Prove that it is equivalent to the existing
    semantics.
 
    Hint: we just proved that [eval] and [multistep] are
    equivalent, so logically it doesn't matter which you choose.
    One will be easier than the other, though!  *)

Lemma evalF_exists:
  forall t, exists n, evalF t = n.
Proof.
  induction t.
  exists n; constructor.
  inversion IHt1; inversion IHt2.
  exists (x + x0).
  simpl. auto.
Qed.

Theorem evalF_eval : forall t n,
  evalF t = n <-> t || n.
Proof.
  split; generalize dependent n.
  induction t; intros.
  simpl in H; rewrite H; constructor.
  simpl in H.
  assert (ef1 := evalF_exists t1).
  assert (ef2 := evalF_exists t2).
  inversion ef1; inversion ef2; clear ef1 ef2.
  rewrite <- H. rewrite H0. rewrite H1.
  apply IHt1 in H0; apply IHt2 in H1.
  constructor; assumption.
  
  induction t; intros.
  inversion H; subst; auto.
  simpl. inversion H; subst.
  apply IHt1 in H2; apply IHt2  in H4.
  auto.
Qed.

(*-- Check --*)
Check evalF_eval : forall t n,
  evalF t = n <-> t || n.

