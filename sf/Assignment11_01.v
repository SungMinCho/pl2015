Require Export Assignment11_00.

(* problem #01: 10 points *)

(** **** Exercise: 2 stars (some_term_is_stuck)  *)
Example some_term_is_stuck :
  exists t, stuck t.
Proof.
  unfold stuck.
  unfold normal_form.
  unfold not.
  exists (tiszero ttrue).
  split; intros.
  inversion H.
  inversion H0; subst.
  inversion H2.
  inversion H.
  inversion H0;subst.
  inversion H0;subst.
Qed.

(*-- Check --*)
Check some_term_is_stuck :
  exists t, stuck t.

