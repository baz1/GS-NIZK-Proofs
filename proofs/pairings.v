(* NIZK Proof System - Type 3 pairings defintions and properties by Rémi Bazin *)

Load Fp.




(* Bilinear groups and a few constants *)
Inductive G1 : Set :=
  | ConstrG1 : Fp -> G1.
Inductive G2 : Set :=
  | ConstrG2 : Fp -> G2.
Inductive GT : Set :=
  | ConstrGT : Fp -> GT.

Definition G1_O : G1 := ConstrG1 Fp_0.
Definition G2_O : G2 := ConstrG2 Fp_0.
Definition GT_1 : GT := ConstrGT Fp_0.




(* Group operations *)

Definition addG1 (a b:G1) : G1 :=
  match a with | ConstrG1 va =>
    match b with | ConstrG1 vb =>
      ConstrG1 (addFp va vb)
    end
  end
.

Definition multG1 (a:Fp) (b:G1) : G1 :=
  match b with | ConstrG1 vb =>
    ConstrG1 (multFp a vb)
  end
.

Definition addG2 (a b:G2) : G2 :=
  match a with | ConstrG2 va =>
    match b with | ConstrG2 vb =>
      ConstrG2 (addFp va vb)
    end
  end
.

Definition multG2 (a:Fp) (b:G2) : G2 :=
  match b with | ConstrG2 vb =>
    ConstrG2 (multFp a vb)
  end
.

Definition multGT (a b:GT) : GT :=
  match a with | ConstrGT va =>
    match b with | ConstrGT vb =>
      ConstrGT (addFp va vb)
    end
  end
.

Definition powGT (a:GT) (b:Fp) : GT :=
  match a with | ConstrGT va =>
    ConstrGT (multFp va b)
  end
.

Definition pairing (a:G1) (b:G2) : GT :=
  match a with | ConstrG1 va =>
    match b with | ConstrG2 vb =>
      ConstrGT (multFp va vb)
    end
  end
.




(* Mathematical structure properties *)

Theorem G1_well_formed : (Is_Fp_isomorphic G1 addG1 p).
Proof.
  admit. (* TODO *)
Qed.

Theorem G2_well_formed : (Is_Fp_isomorphic G2 addG2 p).
Proof.
  admit. (* TODO *)
Qed.

Theorem GT_well_formed : (Is_Fp_isomorphic GT multGT p).
Proof.
  admit. (* TODO *)
Qed.

Theorem pairing_bilinear_l : forall (a:G1) (b:G2) (i:Fp),
  pairing (multG1 i a) b = powGT (pairing a b) i.
Proof.
  intros.
  case a, b.
  unfold pairing, multG1, powGT.
  admit. (* TODO *)
Qed.

Theorem pairing_bilinear_r : forall (a:G1) (b:G2) (j:Fp),
  pairing a (multG2 j b) = powGT (pairing a b) j.
Proof.
  admit. (* TODO *)
Qed.

Theorem pairing_bilinear : forall (a:G1) (b:G2) (i j:Fp),
  pairing (multG1 i a) (multG2 j b) = powGT (pairing a b) (multFp i j).
Proof.
  admit. (* TODO *)
Qed.