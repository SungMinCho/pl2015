Require Export Assignment05_17.

(* problem #18: 10 points *)





(** 1 star (gorgeous_plus13)  *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros. replace (13 + n) with (5 + (5 + (3 + n))).
  constructor 3. constructor 3. constructor. apply H.
  apply plus_assoc.
Qed.
(** [] *)




