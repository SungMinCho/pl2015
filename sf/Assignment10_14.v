Require Export Assignment10_13.

(* problem #14: 10 points *)

(* Hint: 

   First study the chapter "Auto.v".

   Using [;], [try] and [eauto], you can prove it in 4 lines thanks to: 
     Hint Constructors aval
     Hint Constructors astep.
  
   You can use the following intro pattern:
     destruct ... as [[? ?] | [? ?]].
*)

Hint Constructors aval.
Hint Constructors astep.

Theorem aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.
Proof.
  induction a; eauto; right;
  inversion IHa1 as [[n N] | [a1' A1']];
  inversion IHa2 as [[m M] | [a2' A2']];
  subst; eexists; eauto.
Qed.

(*-- Check --*)
Check aexp_strong_progress: forall st a,
  (exists n, a = ANum n) \/
  exists a', a / st ==>a a'.

