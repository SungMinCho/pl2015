Require Export Assignment09_11.

(* problem #12: 10 points *)

(** **** Exercise: 2 stars, advanced (hoare_asgn_weakest)  *)
(** Show that the precondition in the rule [hoare_asgn] is in fact the
    weakest precondition. *)

Theorem hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
Proof.
  unfold is_wp. unfold hoare_triple. split;intros.
  inversion H;subst. auto.
  unfold assert_implies;intros.
  assert (HH := H st (update st X (aeval st a))).
  assert ((X ::= a) / st || update st X (aeval st a)).
  apply E_Ass. auto.
  apply HH in H1; try assumption.
Qed.

(*-- Check --*)
Check hoare_asgn_weakest : forall Q X a,
  is_wp (Q [X |-> a]) (X ::= a) Q.
