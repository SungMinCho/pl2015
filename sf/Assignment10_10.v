Require Export Assignment10_09.

(* problem #10: 10 points *)

(** The fact that small-step reduction implies big-step is now
    straightforward to prove, once it is stated correctly. 

    The proof proceeds by induction on the multi-step reduction
    sequence that is buried in the hypothesis [normal_form_of t t']. *)
(** Make sure you understand the statement before you start to
    work on the proof.  *)

Lemma exists_n : forall t, exists n, t || n.
Proof.
  induction t.
  exists n; constructor.
  inversion IHt1; inversion IHt2.
  exists (x + x0); constructor; assumption.
Qed.

(** **** Exercise: 3 stars (multistep__eval)  *)
Theorem multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.
Proof.
  intros.
  assert (HN := exists_n t).
  inversion HN.
  exists x.
  inversion H.
  assert (EMS := eval__multistep t x).
  assert (HH := H0).
  apply EMS in H0. clear EMS.
  split; try assumption.
  assert (nfu := normal_forms_unique t t' (C x)).
  apply nfu; try assumption.
  unfold normal_form_of.
  split; try assumption.
  unfold step_normal_form; unfold normal_form; unfold not; intros.
  inversion H3. inversion H4.
Qed.

(*-- Check --*)
Check multistep__eval : forall t t',
  normal_form_of t t' -> exists n, t' = C n /\ t || n.

