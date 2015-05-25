Require Export Assignment09_06.

(* problem #07: 10 points *)

(** **** Exercise: 3 stars, optional (add_slowly_decoration)  *)
(** The following program adds the variable X into the variable Z
    by repeatedly decrementing X and incrementing Z.
    {{X + Z = n + m}}
  WHILE X <> 0 DO
     Z ::= Z + 1;;
     X ::= X - 1
  END
    {{X + Z = n + m /\ X = 0}} ->>
    {{Z = n + m}}

    Following the pattern of the [subtract_slowly] example above, pick
    a precondition and postcondition that give an appropriate
    specification of [add_slowly]; then (informally) decorate the
    program accordingly. *)

Theorem slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.
Proof.
  intros.
  apply hoare_consequence with (P' := (fun st:state => st X + st Y = n + m))
  (Q' := (fun st:state => st X + st Y = n + m /\ beval st (BNot (BEq (AId X) (ANum 0))) = false)).
  apply hoare_while. unfold hoare_triple. intros. inversion H0. rewrite <- H1.
  inversion H. subst. inversion H5; subst. inversion H8;subst. unfold update. simpl in *.
  apply negb_true in H2. apply beq_nat_false in H2. omega.
  unfold assert_implies; intros; inversion H; subst; omega.
  unfold assert_implies; intros; inversion H. rewrite <- H0.
  simpl in H1. apply negb_false in H1. apply beq_nat_true in H1. omega.
Qed.

(*-- Check --*)
Check slow_addition_dec_correct : forall n m,
  {{fun st => st X = n /\ st Y = m }}
  WHILE BNot (BEq (AId X) (ANum 0)) DO
     Y ::= APlus (AId Y) (ANum 1);;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{fun st => st Y = n + m}}.

