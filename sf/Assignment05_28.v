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
| pal_nil : pal []
| pal_single : forall x : X, pal [x]
| pal_add : forall (lst : list X) (x : X), pal lst -> pal (x :: (snoc lst x))
.

Lemma app_snoc :
forall (X:Type) (la lb : list X) (x : X),
  la ++ (snoc lb x) = (snoc (la ++ lb) x).
Proof.
  induction la. reflexivity. intros.
  simpl. rewrite IHla. reflexivity.
Qed.

Theorem pal_app_rev: forall (X: Type) (l: list X),
  pal (l ++ rev l).
Proof.
  intros. induction l. simpl. constructor.
  simpl. rewrite app_snoc. constructor. apply IHl.
Qed.

Lemma rev_snoc :
forall (X:Type) (lst:list X) (x:X), rev (snoc lst x) = x :: (rev lst).
Proof.
  induction lst. reflexivity. intros.
  simpl. rewrite IHlst. reflexivity.
Qed.

Theorem pal_rev: forall (X: Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros. induction H. reflexivity. reflexivity.
  simpl. rewrite rev_snoc. simpl. rewrite <- IHpal. reflexivity.
Qed.

(** [] *)




