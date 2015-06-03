Require Export Assignment10_04.

(* problem #05: 10 points *)

Hint Constructors step.

(** **** Exercise: 2 stars (test_multistep_4)  *)
Lemma test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).
Proof.
eapply multi_step.
apply ST_Plus2.
constructor.
apply ST_Plus2.
constructor.
eauto.
eapply multi_step.
apply ST_Plus2.
constructor.
eauto.
constructor.
Qed.

(*-- Check --*)
Check test_multistep_4:
      P
        (C 0)
        (P
          (C 2)
          (P (C 0) (C 3)))
  ==>*
      P
        (C 0)
        (C (2 + (0 + 3))).

