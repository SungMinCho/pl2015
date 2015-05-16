Require Export Assignment08_03.

(* problem #04: 10 points *)

(** **** Exercise: 4 stars (no_whiles_terminating)  *)
(** Imp programs that don't involve while loops always terminate.
    State and prove a theorem [no_whiles_terminating] that says this. *)

(* Hint *)
Check andb_true_iff.

Theorem no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.
Proof.
  intros. generalize dependent st. induction c; intros. 
  exists st; constructor.
  exists (update st i (aeval st a)); constructor; reflexivity.
  inversion NOWHL; apply andb_true_iff in H0; destruct H0.
  apply IHc1 with st in H. inversion H.
  apply IHc2 with x in H0. inversion H0. exists x0. apply E_Seq with x; assumption.
  inversion NOWHL; apply andb_true_iff in H0; destruct H0.
  apply IHc1 with st in H. inversion H.
  apply IHc2 with st in H0. inversion H0.
  destruct (beval st b) eqn:E. exists x. apply E_IfTrue; assumption.
  exists x0. apply E_IfFalse; assumption.
  inversion NOWHL.
Qed.

(*-- Check --*)
Check no_whiles_terminate: forall c st
    (NOWHL: no_whiles c = true),
  exists st', c / st || st'.

