Require Export Assignment05_27.

(* problem #28: 30 points *)


(** 4 stars (palindromes)  *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
        c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove [pal_app_rev] that 
       forall l, pal (l ++ rev l).
    - Prove [pal_rev] that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X: Type} : list X -> Prop :=
  palc : forall l, l = rev l -> pal l
.

Lemma app_nil : forall (X:Type) (l:list X), l ++ [] = l.
Proof. induction l. reflexivity. simpl. rewrite IHl. reflexivity. Qed.

Lemma snoc_app : forall (X:Type) (la lb:list X) (x : X),
  snoc (la ++ lb) x = la ++ snoc lb x.
Proof. induction la. reflexivity. intros. simpl. rewrite IHla.
reflexivity. Qed.

Lemma rev_app : forall (X:Type) (la lb:list X), rev (la ++ lb) = (rev lb) ++ (rev la).
Proof.
  induction la. simpl. intro. rewrite app_nil. reflexivity.
  simpl. intro. rewrite IHla. apply snoc_app. Qed.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros. constructor. rewrite rev_app. rewrite rev_involutive. reflexivity.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros. inversion H. apply H0.
Qed.

(** [] *)




