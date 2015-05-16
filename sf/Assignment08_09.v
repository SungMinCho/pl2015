Require Export Assignment08_08.

(* problem #09: 10 points *)

(** **** Exercise: 2 stars (WHILE_true)  *)
(** Prove the following theorem. _Hint_: You'll want to use
    [WHILE_true_nonterm] here. *)

Lemma WHILE_true_nonterm : forall st st' c, (WHILE BTrue DO c END) / st || st' -> False.
Proof.
  intros st st' c contra.
  remember (WHILE BTrue DO c END) as loopdef eqn:Heqloopdef.
  induction contra; inversion Heqloopdef.
  subst. inversion H. subst. apply IHcontra2 in Heqloopdef. inversion Heqloopdef. Qed.

Theorem WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).
Proof. 
  intros. apply CWhile_congruence with b BTrue c c in H; try (apply refl_cequiv).
  apply trans_cequiv with (WHILE BTrue DO c END); try (apply H). clear H.
  split; intros; apply WHILE_true_nonterm in H; inversion H.
Qed.

(*-- Check --*)
Check WHILE_true: forall b c,
     bequiv b BTrue  ->
     cequiv 
       (WHILE b DO c END)
       (WHILE BTrue DO SKIP END).

