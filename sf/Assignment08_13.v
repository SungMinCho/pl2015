Require Export Assignment08_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars (CIf_congruence)  *)
Theorem CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).
Proof.
  split; intros; unfold bequiv in *. 
  inversion H2; subst.
  try (apply E_IfTrue; try (symmetry; rewrite <- H8; apply H); apply H0; assumption).
  try (apply E_IfFalse; try (symmetry; rewrite <- H8; apply H); apply H1; assumption).
  inversion H2; subst.
  try (apply E_IfTrue; try (rewrite <- H8; apply H); apply H0; assumption).
  try (apply E_IfFalse; try (rewrite <- H8; apply H); apply H1; assumption).
Qed.

(*-- Check --*)
Check CIf_congruence : forall b b' c1 c1' c2 c2',
  bequiv b b' -> cequiv c1 c1' -> cequiv c2 c2' ->
  cequiv (IFB b THEN c1 ELSE c2 FI) (IFB b' THEN c1' ELSE c2' FI).

