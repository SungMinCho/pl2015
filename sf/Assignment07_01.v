Require Export Assignment07_00.

(* problem #01: 20 points *)


(** **** Exercise: 3 stars (optimize_0plus_b)  *)
(** Since the [optimize_0plus] tranformation doesn't change the value
    of [aexp]s, we should be able to apply it to all the [aexp]s that
    appear in a [bexp] without changing the [bexp]'s value.  Write a
    function which performs that transformation on [bexp]s, and prove
    it is sound.  Use the tacticals we've just seen to make the proof
    as elegant as possible. *)

Print bexp.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
match b with
| BTrue => b
| BFalse => b
| BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
| BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
| BNot b1 => BNot (optimize_0plus_b b1)
| BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
end.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
    (* Most cases follow directly by the IH *)
    try (simpl; rewrite IHa1; rewrite IHa2; reflexivity);
    (* ... or are immediate by definition *)
    try reflexivity.
  (* The interesting case is when a = APlus a1 a2. *)
  Case "APlus".
    destruct a1; try (simpl; simpl in IHa1; rewrite IHa1;
                      rewrite IHa2; reflexivity).
    SCase "a1 = ANum n". destruct n;
      simpl; rewrite IHa2; reflexivity. Qed.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
intros b.
induction b; 
try (simpl;repeat (rewrite optimize_0plus_sound));
try (rewrite IHb); try (rewrite IHb1; rewrite IHb2);
try reflexivity.
Qed.
(** [] *)

