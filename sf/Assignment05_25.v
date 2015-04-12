Require Export Assignment05_24.

(* problem #25: 10 points *)









(** 3 stars, optional (ev_plus_plus)  *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. 
    Hint: You can use [plus_comm], [plus_assoc], [double_plus], [double_even], [ev_sum], [ev_ev__ev].
*)
Check plus_comm.
Check plus_assoc.
Check double_plus.
Check double_even.
Check ev_sum.
Check ev_ev__ev.

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros. apply ev_sum with (m := n+p) in H.
  assert (forall a b c d, a + b + (c + d) = a + (b + c) + d).
  intros. rewrite plus_assoc. rewrite plus_assoc. reflexivity.
  rewrite H1 in H. replace (m + n) with (n + m) in H. rewrite <- H1 in H.
  rewrite <- double_plus in H. assert (ev (double n)). apply double_even.
  apply ev_ev__ev with (n:=double n) (m:=m+p). apply H. apply H2. apply plus_comm. apply H0.
Qed.
(** [] *)


