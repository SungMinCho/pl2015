Require Export Assignment10_12.

(* problem #13: 10 points *)

(** **** Exercise: 3 stars, optional  *)
Lemma par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.
Proof.
  intros.
  inversion H; clear H.
  induction n.
  exists st. split. constructor. split; assumption.
  inversion IHn. inversion H. inversion H3.
  exists (update x X (S n)).
  split.
  eapply multi_trans. apply H2.
  apply par_body_n__Sn.
  split; assumption.
  split; auto.
Qed.

(*-- Check --*)
Check par_body_n : forall n st,
  st X = 0 /\ st Y = 0 ->
  exists st',
    par_loop / st ==>c*  par_loop / st' /\ st' X = n /\ st' Y = 0.

