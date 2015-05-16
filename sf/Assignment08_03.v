Require Export Assignment08_02.

(* problem #03: 10 points *)

(** **** Exercise: 3 stars (loop_never_stops)  *)
Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  subst. inversion H. subst. apply IHcontra2 in Heqloopdef. inversion Heqloopdef.
Qed.

(*-- Check --*)
Check loop_never_stops : forall st st',
  ~(loop / st || st').

