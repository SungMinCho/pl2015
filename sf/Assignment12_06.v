Require Export Assignment12_05.

(* problem #06: 10 points *)  

Notation FA := (tapp tloop (tnat 0)).
Notation FB := (
tapp
  (tapp
     (tabs Loop (TArrow TNat TNat) (tabs X TNat (tapp (tvar Loop) (tvar X))))
     (tfix
        (tabs Loop (TArrow TNat TNat)
           (tabs X TNat (tapp (tvar Loop) (tvar X)))))) (tnat 0)).
Notation FC := (tapp
  ([Loop
   := tfix
        (tabs Loop (TArrow TNat TNat)
           (tabs X TNat (tapp (tvar Loop) (tvar X))))]
   tabs X TNat (tapp (tvar Loop) (tvar X))) (tnat 0)
).

Lemma AB : FA ==> FB.
Proof.
apply ST_AppFix; eauto. Qed.
Lemma BC : FB ==> FC.
Proof.
apply ST_App1; eauto. Qed.
Lemma CA : FC ==> FA.
Proof.
apply ST_AppAbs;eauto. Qed.

Inductive nstep : tm -> nat -> tm -> Prop :=
| nstep0 : forall S, nstep S 0 S 
| nstepS : forall T TT TTT n,
   T ==> TT -> nstep TT n TTT -> nstep T (S n) TTT.

Lemma multi_n :
forall t t1, t ==>* t1 -> exists n, nstep t n t1.
Proof.
intros.
induction H. exists 0; constructor.
inversion IHmulti as [n p]. exists (S n).
eapply nstepS. apply H. assumption. Qed.

Lemma A_B:
forall t, FA ==> t -> t = FB.
Proof.
  intros.
  inversion H;subst;try auto.
  inversion H3;subst.
  inversion H1;subst.
  inversion H4.
Qed.

Lemma B_C:
forall t, FB ==> t -> t = FC.
Proof.
  intros.
  inversion H;subst;auto.
  inversion H3;subst.
  auto.
  inversion H4;subst.
  inversion H5;subst.
  inversion H1;subst.
  inversion H4.
Qed.

Lemma C_A:
forall t, FC ==> t -> t = FA.
Proof.
  intros.
  inversion H; subst; try auto.
  inversion H3;subst; try auto.
  inversion H4.
Qed.

Lemma ABC_n :
forall n t, nstep FA n t \/ nstep FB n t \/ nstep FC n t
-> t = FA \/ t = FB \/ t = FC.
Proof.
induction n; intros. 
inversion H as [P | [P | P]];
inversion P;subst;auto.
inversion H as [P | [P | P]].
inversion P; subst. apply A_B in H1. subst.
assert (nstep FA n t \/ nstep FB n t \/ nstep FC n t). auto.
apply IHn in H0. auto.
inversion P; subst. apply B_C in H1; subst.
assert (nstep FA n t \/ nstep FB n t \/ nstep FC n t). auto.
apply IHn in H0. auto.
inversion P; subst. apply C_A in H1; subst.
assert (nstep FA n t \/ nstep FB n t \/ nstep FC n t). auto.
apply IHn in H0. auto.
Qed.


Lemma ABC :
forall t, FA ==>* t -> t = FA \/ t = FB \/ t = FC.
Proof.
  intros.
  assert (HH := multi_n FA t).
  apply HH in H.
  inversion H.
  assert (nstep FA x t \/ nstep FB x t \/ nstep FC x t). auto.
  apply ABC_n in H1. auto.
Qed.

Theorem tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.
Proof.
  unfold not. intros.
  inversion H.
  destruct H0. clear H.
  unfold normal_form in H1.
  unfold not in H1.
  apply ABC in H0.
  apply H1.
  inversion H0 as [X | [Y | Z]].
  exists FB. rewrite X. apply AB.
  exists FC. rewrite Y. apply BC.
  exists FA. rewrite Z. apply CA.
Qed.

(*-- Check --*)
Check tloop_diverges:
  ~ exists t, tapp tloop (tnat 0) ==>* t /\ normal_form step t.

