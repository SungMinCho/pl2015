Require Export Assignment10_15.

(* problem #16: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 6 lines thanks to:
     Hint Constructors cstep.
 
   You can use the following intro pattern:
     destruct ... as [ | [? [? ?]]].
*)

Hint Constructors cstep.

Theorem cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.
Proof.
  intros.
  induction c; eauto; right; try(
  assert (H := aexp_strong_progress st a);
  inversion H as [[n N] | [a' A']]; subst; eauto); try(
  try (assert (H := bexp_strong_progress st b);
       inversion H as [[b0 | b1] | [bb BB]]);
  inversion IHc1 as [C1 | [a [b' c]]];
  inversion IHc2 as [C2 | [d [e f]]];
  subst; eauto).
Qed.

(*-- Check --*)
Check cimp_strong_progress : forall c st,
  c = SKIP \/ 
  exists c' st', c / st ==>c c' / st'.

