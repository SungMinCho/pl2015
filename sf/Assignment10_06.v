Require Export Assignment10_05.

(* problem #06: 10 points *)

Theorem normal_forms_unique:
  deterministic normal_form_of.
Proof.
  unfold deterministic. unfold normal_form_of.  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1. inversion P2 as [P21 P22]; clear P2. 
  generalize dependent y2. 
  (* We recommend using this initial setup as-is! *)
  induction P11; intros.
  inversion P21; subst.
  auto.
  assert (exists t', x ==> t'). exists y; assumption.
  apply P12 in H1. inversion H1.
  apply IHP11; try assumption.
  inversion P21; subst.
  assert (exists t', y2 ==> t'). exists y; assumption.
  apply P22 in H0. inversion H0.
  assert (y0y := step_deterministic_alt x y0 y).
  assert (y0 = y). apply y0y; assumption.
  subst.
  assumption.
Qed.

(*-- Check --*)
Check normal_forms_unique:
  deterministic normal_form_of.

