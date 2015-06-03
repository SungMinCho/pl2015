Require Export Assignment10_14.

(* problem #15: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 7 lines thanks to:. 
     Hint Constructors bstep.

   You can use the following intro pattern:
     destruct ... as [[? | ?] | [? ?]].
*)

Hint Constructors bstep.

Theorem bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.
Proof.
  induction b; eauto; right; try(
  assert (H1 := aexp_strong_progress st a);
  assert (H2 := aexp_strong_progress st a0);
  inversion H1 as [[n N] | [a' A']];
  inversion H2 as [[n0 N0] | [a0' A0']];
  subst; eexists; eauto).
  inversion IHb as [[x | y] | [z w]]; subst; eauto.
  inversion IHb1 as [[x | y] | [z w]];
  inversion IHb2 as [[x2 | y2] | [z2 w2]]; subst; eauto.
Qed.

(*-- Check --*)
Check bexp_strong_progress: forall st b,
  (b = BTrue \/ b = BFalse) \/
  exists b', b / st ==>b b'.

