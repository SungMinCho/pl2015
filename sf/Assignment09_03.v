Require Export Assignment09_02.

(* problem #03: 10 points *)

(** **** Exercise: 4 stars (hoare_asgn_wrong)  *)
(** The assignment rule looks backward to almost everyone the first
    time they see it.  If it still seems backward to you, it may help
    to think a little about alternative "forward" rules.  Here is a
    seemingly natural one:
      ------------------------------ (hoare_asgn_wrong)
      {{ True }} X ::= a {{ X = a }}
    Give a counterexample showing that this rule is incorrect
    (informally). Hint: The rule universally quantifies over the
    arithmetic expression [a], and your counterexample needs to
    exhibit an [a] for which the rule doesn't work. *)

Theorem hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.
Proof.
  exists (APlus (AId X) (ANum 1)). unfold not. unfold hoare_triple. intros.
  assert (HH := H empty_state (update empty_state X 1)).
  assert ((X ::= APlus (AId X) (ANum 1)) / empty_state || update empty_state X 1).
  apply E_Ass; reflexivity. apply HH in H0. unfold update in H0. simpl in H0. inversion H0. auto.
Qed.

(*-- Check --*)
Check hoare_asgn_wrong:
  exists a, ~ {{ fun st => True }} X ::= a {{ fun st => st X = aeval st a}}.

