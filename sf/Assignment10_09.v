Require Export Assignment10_08.

(* problem #09: 10 points *)

(** **** Exercise: 3 stars (step__eval)  *)
Lemma step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.
Proof.
  intros t t' n Hs. generalize dependent n.
  induction Hs; intros.
  inversion H; subst.
  constructor; constructor.
  inversion H; subst.
  apply IHHs in H2.
  constructor; assumption.
  inversion H0; subst.
  apply IHHs in H5.
  constructor; assumption.
Qed.

(*-- Check --*)
Check step__eval : forall t t' n,
     t ==> t' ->
     t' || n ->
     t || n.

