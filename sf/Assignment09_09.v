Require Export Assignment09_08.

(* problem #09: 10 points *)

(** **** Exercise: 4 stars (factorial)  *)
(** Recall that [n!] denotes the factorial of [n] (i.e. [n! =
    1*2*...*n]).  Here is an Imp program that calculates the factorial
    of the number initially stored in the variable [X] and puts it in
    the variable [Y]:
    {{ X = m }} 
  Y ::= 1 ;;
  WHILE X <> 0
  DO
     Y ::= Y * X ;;
     X ::= X - 1
  END
    {{ Y = m! }}

    Fill in the blanks in following decorated program:
    {{ X = m }} ->>
    {{ X! * Y = m!  [Y |-> 1]                  }}
  Y ::= 1;;
    {{ X! * Y = m!                             }}
  WHILE X <> 0
  DO   {{  X! * Y = m!  /\   X <> 0            }} ->>
       {{ (X! * Y = m! [X |-> X-1]) [Y |-> Y*X]   }}
     Y ::= Y * X;;
       {{  X! * Y = m! [X |-> X-1]           }}
     X ::= X - 1
       {{  X! * Y = m!                         }}
  END
    {{  X! * Y = m!  /\    X = 0             }} ->>
    {{ Y = m! }}
*)

Print fact.

Theorem factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.
Proof.
  intros.
  remember (fun st:state => fact (st X) * st Y = fact m) as V.
  apply hoare_consequence with
  (P' := V [Y |-> (ANum 1)])
  (Q' := (fun st:state => V st /\ beval st (BNot (BEq (AId X) (ANum 0))) = false)).
  apply hoare_seq with V.
  apply hoare_while.
  unfold hoare_triple;intros. inversion H0.
  inversion H; subst. rewrite <- H1. simpl in H2.
  apply negb_true in H2. apply beq_nat_false in H2. 
  inversion H5;subst. inversion H8;subst. unfold update.
  simpl. destruct (st X). absurd (0=0); auto. simpl.
  rewrite <- minus_n_O. 
  replace (st Y * S n) with (S n * st Y);try (apply mult_comm).
  rewrite mult_assoc. rewrite mult_succ_r.
  rewrite plus_comm. 
  replace (fact n * n) with (n * fact n);try (apply mult_comm).
  auto. 
  apply hoare_asgn. 
  unfold assert_implies;intros.
  unfold assn_sub. unfold update. subst. simpl. omega.
  unfold assert_implies;intros.
  inversion H. simpl in H1. apply negb_false in H1.
  apply beq_nat_true in H1. subst. rewrite H1 in  H0.
  simpl in H0. omega.
Qed.

(*-- Check --*)
Check factorial_dec_correct: forall m,
  {{ fun st => st X = m }} 
  Y ::= ANum 1 ;;
  WHILE BNot (BEq (AId X) (ANum 0))
  DO
     Y ::= AMult (AId Y) (AId X) ;;
     X ::= AMinus (AId X) (ANum 1)
  END
  {{ fun st => st Y = fact m }}.

