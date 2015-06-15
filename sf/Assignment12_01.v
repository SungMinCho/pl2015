Require Export Assignment12_00.

(* problem #01: 10 points *)

(** **** Exercise: 3 stars, optional (typing_nonexample_3)  *)
(** Another nonexample:
    ~ (exists S, exists T,
          empty |- \x:S. x x : T).
*)

Lemma stupid:
  forall T1 T2, ~ T1 = TArrow T1 T2.
Proof.
  unfold not.
  intros.
  generalize dependent T2.
  induction T1; intros; inversion H.
  apply IHT1_1 in H1; assumption.
Qed.

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).
Proof.
  unfold not; intros.
  inversion H as [S [T p]].
  inversion p; subst.
  inversion H5;subst.
  inversion H6;subst.
  unfold extend in H2.
  simpl in H2.
  inversion H2;subst.
  inversion H3;subst.
  unfold extend in H4.
  simpl in H4.
  inversion H4.
  apply stupid in H1;assumption.
Qed.

(*-- Check --*)
Check typing_nonexample_3 :
  ~ (exists S, exists T,
        empty |- 
          (tabs X S
             (tapp (tvar X) (tvar X))) \in
          T).

