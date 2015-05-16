Require Export Assignment08_17.

(* problem #18: 10 points *)

Lemma optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.
Proof.
  unfold ctrans_sound. induction c; try (apply refl_cequiv).
  simpl. assert (H := optimize_0plus_aexp_sound a). apply CAss_congruence; assumption. simpl.
  apply CSeq_congruence; assumption. simpl. assert (H := optimize_0plus_bexp_sound b).
  apply CIf_congruence; assumption.
  apply CWhile_congruence. apply optimize_0plus_bexp_sound.
  destruct c; try (apply refl_cequiv); try assumption.
Qed.

(*-- Check --*)
Check optimize_0plus_com_sound:
  ctrans_sound optimize_0plus_com.

