Require Export Assignment06_07.

(* problem #08: 40 points *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle)  *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  induction l1. reflexivity.
  intros. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros. induction H. exists []. exists l. reflexivity.
  inversion IHappears_in. inversion proof.
  exists (b::witness). exists witness0. simpl. rewrite proof0.
  reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| repeats_here : forall n lst, appears_in n lst -> repeats (n::lst)
| repeats_later : forall n lst, repeats lst -> repeats (n::lst)
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros. induction H0. apply H. constructor. apply IHle.
Qed.



Lemma Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros. inversion H. constructor. 
  assert (n <= S n). constructor. constructor. apply le_trans with (S n).
  apply H2. apply H1.
Qed.



Lemma Sn_lt_Sm__n_lt_m : forall n m, S n < S m -> n < m.
Proof. unfold lt. intros. apply Sn_le_Sm__n_le_m. apply H. Qed.


Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X), 
   excluded_middle -> 
   (forall x, appears_in x l1 -> appears_in x l2) -> 
   length l2 < length l1 -> 
   repeats l1.  
Proof.
   intros X l1. induction l1 as [|x l1'].
   intros. inversion H1. intros.
   assert (forall l : list X,
        (forall x0 : X, appears_in x0 l1' -> appears_in x0 l) ->
        length l < length l1' -> repeats l1').
   intros. apply IHl1' with l. apply H. apply H2. apply H3. clear IHl1'.
   assert (appears_in x l1' \/ ~ appears_in x l1'). apply H.
   inversion H3. constructor. apply H4.
   assert (appears_in x l2). apply H0. constructor.
   apply appears_in_app_split in H5. inversion H5 as [d1 p]. inversion p as [d2 proof].
   symmetry in proof. assert (length (d1 ++ x :: d2) = length l2).
   rewrite proof. reflexivity. rewrite app_length in H6.
   simpl in H6. rewrite <- plus_n_Sm in H6. rewrite <- H6 in H1.
   simpl in H1. apply Sn_lt_Sm__n_lt_m in H1. constructor 2.
   apply H2 with (d1++d2). intros. assert (x0 <> x). intro. rewrite H8 in H7.
   apply H4 in H7. inversion H7. assert (appears_in x0 (x :: l1')). constructor. apply H7.
   apply H0 in H9. rewrite <- proof in H9. apply appears_in_app in H9.
   inversion H9. apply app_appears_in. left. apply H10.
   inversion H10. apply H8 in H12. inversion H12. apply app_appears_in. right. apply H12.
   rewrite app_length. apply H1.
Qed.

