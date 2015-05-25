Require Export Assignment09_04.

(* problem #05: 10 points *)

(** **** Exercise: 2 stars (if_minus_plus)  *)
(** Prove the following hoare triple using [hoare_if]: *)

Theorem if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 
Proof.
  remember (BLe (AId X) (AId Y)) as b. remember (fun st:state => st Y = st X + st Z) as F.
  remember (F [Z |-> AMinus (AId Y) (AId X)]) as Q1. remember (F [Y |-> APlus (AId X) (AId Z)]) as Q2.
  apply hoare_consequence_pre with 
  (P' := (fun st:state => (beval st b = true -> Q1 st) /\ (beval st b = false -> Q2 st))).
  apply hoare_if; subst; apply hoare_asgn.
  unfold assert_implies. intros. split;subst;intros;unfold assn_sub;unfold update;simpl.
  inversion H0. apply ble_nat_true in H2. symmetry. omega. reflexivity.
Qed.

(*-- Check --*)
Check if_minus_plus :
  {{fun st => True}}
  IFB (BLe (AId X) (AId Y))
    THEN (Z ::= AMinus (AId Y) (AId X))
    ELSE (Y ::= APlus (AId X) (AId Z))
  FI
  {{fun st => st Y = st X + st Z}}. 

