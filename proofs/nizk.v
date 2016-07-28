(* NIZK Proof System - verification script by Remi Bazin *)

Load pairings.





(* Bilinear groups and a few constants *)
Inductive B1 : Set :=
  | ConstrB1 : G1 -> G1 -> B1.
Inductive B2 : Set :=
  | ConstrB2 : G2 -> G2 -> B2.
Inductive BT : Set :=
  | ConstrBT : GT -> GT -> GT -> GT -> BT.

Definition B1_O : B1 := ConstrB1 G1_O G1_O.
Definition B2_O : B2 := ConstrB2 G2_O G2_O.
Definition BT_1 : BT := ConstrBT GT_1 GT_1 GT_1 GT_1.




(* Group operations *)

Definition addB1 (a b:B1) : B1 :=
  match a with | ConstrB1 a1 a2 =>
    match b with | ConstrB1 b1 b2 =>
      ConstrB1 (addG1 a1 b1) (addG1 a2 b2)
    end
  end
.

Definition addB2 (a b:B2) : B2 :=
  match a with | ConstrB2 a1 a2 =>
    match b with | ConstrB2 b1 b2 =>
      ConstrB2 (addG2 a1 b1) (addG2 a2 b2)
    end
  end
.

Definition multBT (a b:BT) : BT :=
  match a with | ConstrBT a1 a2 a3 a4 =>
    match b with | ConstrBT b1 b2 b3 b4 =>
      ConstrBT (multGT a1 b1) (multGT a2 b2) (multGT a3 b3) (multGT a4 b4)
    end
  end
.





(* Mathematical structure properties *)
Theorem B1_abelian : (Is_Fp_isomorphic B1 addB1 p).
Proof.
  admit. (* TODO *)
Qed.

Theorem B2_abelian : (Is_Fp_isomorphic B2 addB2 p).
Proof.
  admit. (* TODO *)
Qed.

Theorem BT_abelian : (Is_Fp_isomorphic BT multBT p).
Proof.
  admit. (* TODO *)
Qed.
