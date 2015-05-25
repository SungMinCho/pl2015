Require Export Assignment09_05.

(* problem #06: 10 points *)

(** **** Exercise: 2 stars (slow_assignment)  *)
(** A roundabout way of assigning a number currently stored in [X] to
    the variable [Y] is to start [Y] at [0], then decrement [X] until
    it hits [0], incrementing [Y] at each step. Here is a program that
    implements this idea:
      {{ X = m }}
    Y ::= 0;;
      {{ X + Y = m }}
    WHILE X <> 0 DO
      X ::= X - 1;;
      Y ::= Y + 1
    END
      {{ X + Y = m /\ X = 0}} ->>
      {{ Y = m }} 
    Write an informal decorated program showing that this is correct. *)

Theorem slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
Proof. 
  intros.
  remember (BNot (BEq (AId X) (ANum 0))) as b. remember (fun st:state => st X + st Y = m) as P.
  apply hoare_consequence_post with (Q' := (fun st:state => P st /\ beval st b = false)).
  apply hoare_seq with (Q := P). apply hoare_while. unfold hoare_triple. intros. subst.
  inversion H0;subst. inversion H;subst. inversion H7;subst. inversion H4; subst.
  unfold update;simpl. simpl in H2. apply negb_true in H2. apply beq_nat_false in H2.
  destruct (st X). absurd (0<>0);eauto. omega. 
  apply hoare_consequence_pre with (P' := P [Y |-> ANum 0]). apply hoare_asgn.
  unfold assert_implies. unfold assn_sub. unfold update. intros. subst. simpl. omega.
  unfold assert_implies. intros. inversion H. subst. simpl in H1.
  apply negb_false in H1. apply beq_nat_true in H1. rewrite H1 in *. assumption.
Qed.

(*-- Check --*)
Check slow_assignment : forall m,
    {{ fun st => st X = m }}
    Y ::= ANum 0;;
    WHILE BNot (BEq (AId X) (ANum 0)) DO
      X ::= AMinus (AId X) (ANum 1);;
      Y ::= APlus (AId Y) (ANum 1)
    END
    {{ fun st => st Y = m }}.
  
