Require Export Assignment11_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars, optional (step_deterministic)  *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Hint Constructors step.

Theorem step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros.
  generalize dependent y2.
  induction H; intros;
  try (inversion H0; subst; eauto; inversion H4).
  inversion H0; subst.
  inversion H. inversion H. apply IHstep in H5. subst; eauto.
  inversion H0; subst.
  apply IHstep in H2; subst...
  inversion H0; subst...
  inversion H1.
  assert (value t1); eauto.
  inversion H0;subst...
  assert (value (tsucc t1))...
  apply value_is_nf in H2.
  unfold normal_form in H2.
  unfold not in *.
  assert (exists t', tsucc t1 ==> t')...
  apply H2 in H4; inversion H4.
  inversion H0;subst...
  inversion H.
  assert (value (tsucc y2))...
  apply value_is_nf in H1.
  assert (exists t', tsucc y2 ==> t')...
  apply H1 in H3; inversion H3.
  apply IHstep in H2... subst. auto.
  inversion H0; subst...
  inversion H1.
  inversion H0;subst...
  assert (value (tsucc t1))...
  apply value_is_nf in H1.
  assert (exists t', tsucc t1 ==> t')...
  apply H1 in H3; inversion H3.
  inversion H0; subst.
  inversion H.
  assert (value (tsucc t0))...
  apply value_is_nf in H1.
  assert (exists t', tsucc t0 ==> t')...
  apply H1 in H3; inversion H3.
  apply IHstep in H2; subst; auto.
Qed.

(*-- Check --*)
Check step_deterministic:
  deterministic step.

