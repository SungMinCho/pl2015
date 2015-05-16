Require Export Assignment08_16.

(* problem #17: 10 points *)

Lemma optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.
Proof.
  unfold btrans_sound. induction b; try (apply refl_bequiv); unfold bequiv; intros; simpl;
  try (repeat (rewrite <- optimize_0plus_aexp_sound); reflexivity).
  apply f_equal. unfold bequiv in IHb. assert (H := IHb st). apply H.
  unfold bequiv in *. assert (H1 := IHb1 st); assert (H2 := IHb2 st).
  rewrite <- H1; rewrite <- H2. reflexivity.
Qed.

(*-- Check --*)
Check optimize_0plus_bexp_sound:
  btrans_sound optimize_0plus_bexp.

