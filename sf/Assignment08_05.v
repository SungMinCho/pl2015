Require Export Assignment08_04.

(* problem #05: 20 points *)

(** Write a function which compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Fixpoint s_compile (e : aexp) : list sinstr :=
match e with
| ANum n => [SPush n]
| AId i => [SLoad i]
| APlus a b => (s_compile a)++(s_compile b)++[SPlus]
| AMinus a b => (s_compile a)++(s_compile b)++[SMinus]
| AMult a b => (s_compile a)++(s_compile b)++[SMult]
end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
  reflexivity.
Qed.

(** **** Exercise: 3 stars, advanced (stack_compiler_correct)  *)
(** The task of this exercise is to prove the correctness of the
    compiler implemented in the previous exercise.  Remember that
    the specification left unspecified what to do when encountering an
    [SPlus], [SMinus], or [SMult] instruction if the stack contains
    less than two elements.  (In order to make your correctness proof
    easier you may find it useful to go back and change your
    implementation!)

    Prove the following theorem, stating that the [compile] function
    behaves correctly.  You will need to start by stating a more
    general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_execute_app: forall (st : state) (s1 s2 : list sinstr) (s : list nat),
  s_execute st s (s1 ++ s2) = s_execute st (s_execute st s s1) s2.
Proof.
  induction s1. reflexivity. intros. induction a;try (simpl;rewrite IHs1;reflexivity);
  try (simpl; destruct s; try (destruct s); apply IHs1).
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros. generalize dependent st. generalize ([]:list nat).
  induction e;intros;simpl; try reflexivity;
  try(rewrite s_execute_app; rewrite IHe1;
  rewrite s_execute_app; rewrite IHe2; reflexivity).
Qed.

(*-- Check --*)
Check s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].

Check s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].

