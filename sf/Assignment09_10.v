Require Export Assignment09_09.

(* problem #10: 10 points *)

(** **** Exercise: 3 stars (two_loops)  *)
(** Here is a very inefficient way of adding 3 numbers:
  X ::= 0;;
  Y ::= 0;;
  Z ::= c;;
  WHILE X <> a DO
    X ::= X + 1;;
    Z ::= Z + 1
  END;;
  WHILE Y <> b DO
    Y ::= Y + 1;;
    Z ::= Z + 1
  END

    Show that it does what it should by filling in the blanks in the
    following decorated program.

    {{ True }} ->>
    {{ Z = X + Y + c [Z|->c] [Y|->0] [X|->0] }}
  X ::= 0;;
    {{ Z = X + Y + c [Z|->c] [Y|->0] }}
  Y ::= 0;;
    {{ Z = X + Y + c [Z|->c] }}
  Z ::= c;;
    {{ Z = X + Y + c }}
  WHILE X <> a DO
      {{ Z = X + Y + c /\ X <> a }} ->>
      {{ Z = X + Y + c [Z |-> Z+1] [X |-> X+1] }}
    X ::= X + 1;;
      {{ Z = X + Y + c [Z |-> Z+1] }}
    Z ::= Z + 1
      {{ Z = X + Y + c }}
  END;;
    {{ Z = X + Y + c  /\  X = a  }} ->>
    {{ Z = a + Y + c  }}
  WHILE Y <> b DO
      {{ Z = a + Y + c  /\ Y <> b  }} ->>
      {{ Z = a + Y + c [Z|->Z+1] [Y|->Y+1] }}
    Y ::= Y + 1;;
      {{ Z = a + Y + c [Z|->Z+1]  }}
    Z ::= Z + 1
      {{ Z = a + Y + c  }}
  END
    {{ Z = a + Y + c  /\ Y = b  }} ->>
    {{ Z = a + b + c  }}
*)

Theorem add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.
Proof.
  intros.
  remember (fun st:state => st Z = st X + st Y + c) as V1.
  remember (fun st:state => st Z = a + st Y + c) as V2.
  apply hoare_consequence with
  (V1 [Z|->(ANum c)] [Y|->(ANum 0)] [X|->(ANum 0)])
  (fun st => V2 st /\ beval st (BNot (BEq (AId Y) (ANum b))) = false).
  eapply hoare_seq; try (apply hoare_asgn).
  eapply hoare_seq; try (apply hoare_asgn).
  eapply hoare_seq; try (apply hoare_asgn).
  eapply hoare_seq.
  apply hoare_while. unfold hoare_triple;intros.
  destruct H0. 
  apply negb_true in H1; apply beq_nat_false in H1;simpl in H1.
  inversion H;subst.
  inversion H4;subst;inversion H7;subst;unfold update;simpl. omega.
  eapply hoare_consequence_post.
  apply hoare_while.
  unfold hoare_triple;intros. destruct H0.
  apply negb_true in H1;apply beq_nat_false in H1;simpl in H1.
  inversion H;subst. inversion H4;inversion H7;subst.
  unfold update;simpl. omega.
  unfold assert_implies;intros. destruct H.
  apply negb_false in H0;apply beq_nat_true in H0;simpl in H0.
  subst. omega.
  unfold assert_implies;intros.
  unfold assn_sub. subst;unfold update;simpl. auto.
  unfold assert_implies;intros. destruct H.
  apply negb_false in H0;apply beq_nat_true in H0;simpl in H0.
  subst. omega.
Qed.

(*-- Check --*)
Check add_three_numbers_correct: forall a b c,
  {{ fun st => True }}                                   
  X ::= ANum 0;;
  Y ::= ANum 0;;
  Z ::= ANum c;;
  WHILE BNot (BEq (AId X) (ANum a)) DO
    X ::= APlus (AId X) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END;;
  WHILE BNot (BEq (AId Y) (ANum b)) DO
    Y ::= APlus (AId Y) (ANum 1);;
    Z ::= APlus (AId Z) (ANum 1)
  END
  {{ fun st => st Z = a + b + c }}.

