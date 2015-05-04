Require Export Assignment07_02.

(* problem #03: 20 points *)

(** **** Exercise: 3 stars  (bevalR)  *)
(** Write a relation [bevalR] in the same style as
    [aevalR], and prove that it is equivalent to [beval].*)

Inductive bevalR: bexp -> bool -> Prop :=
| E_BTrue: bevalR BTrue true
| E_BFalse: bevalR BFalse false
| E_BEq: forall a1 a2 n1 n2, 
     a1 || n1 -> a2 || n2 -> bevalR (BEq a1 a2) (beq_nat n1 n2)
| E_BLe: forall a1 a2 n1 n2, 
     a1 || n1 -> a2 || n2 -> bevalR (BLe a1 a2) (ble_nat n1 n2)
| E_BNot: forall B b, bevalR B b -> bevalR (BNot B) (negb b)
| E_BAnd: forall B1 B2 b1 b2,
     bevalR B1 b1 -> bevalR B2 b2 -> bevalR (BAnd B1 B2) (andb b1 b2)
.

Theorem beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
split.
intros.
induction H; simpl;
try (apply aeval_iff_aevalR in H;apply aeval_iff_aevalR in H0;
rewrite H;rewrite H0);
try (rewrite IHbevalR);try (rewrite IHbevalR1;rewrite IHbevalR2);
try reflexivity.
intros. generalize dependent bv.
induction b; intros;
try (simpl in H; rewrite <- H; constructor);
try (apply aeval_iff_aevalR;reflexivity).
assert (negb (negb (beval b)) = negb bv). rewrite H;reflexivity.
rewrite negb_involutive in H0. rewrite H0. apply IHb in H0. assumption.
destruct (beval b1); 
[assert (A := IHb1 true); assert (B := eq_refl true) 
| assert (A := IHb1 false); assert (B := eq_refl false)];
apply A in B; assumption.
destruct (beval b2); 
[assert (A := IHb2 true); assert (B := eq_refl true) 
| assert (A := IHb2 false); assert (B := eq_refl false)];
apply A in B; assumption.
Qed.

(** [] *)

