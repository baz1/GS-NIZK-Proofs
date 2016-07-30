(* NIZK Proof System - Type 3 pairings defintions and properties by Rémi Bazin *)

Load Fp.




(* Bilinear groups and a few constants *)
Inductive G1 : Set :=
  | ConstrG1 : Fp -> G1.
Inductive G2 : Set :=
  | ConstrG2 : Fp -> G2.
Inductive GT : Set :=
  | ConstrGT : Fp -> GT.

Delimit Scope G1_scope with G1.
Delimit Scope G2_scope with G2.
Delimit Scope GT_scope with GT.

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
Infix "+" := addG1 : G1_scope.

Definition multG1 (a:Fp) (b:G1) : G1 :=
  match b with | ConstrG1 vb =>
    ConstrG1 (multFp a vb)
  end
.
Infix "*" := multG1 : G1_scope.

Definition addG2 (a b:G2) : G2 :=
  match a with | ConstrG2 va =>
    match b with | ConstrG2 vb =>
      ConstrG2 (addFp va vb)
    end
  end
.
Infix "+" := addG2 : G2_scope.

Definition multG2 (a:Fp) (b:G2) : G2 :=
  match b with | ConstrG2 vb =>
    ConstrG2 (multFp a vb)
  end
.
Infix "*" := multG2 : G2_scope.

Definition multGT (a b:GT) : GT :=
  match a with | ConstrGT va =>
    match b with | ConstrGT vb =>
      ConstrGT (addFp va vb)
    end
  end
.
Infix "*" := multGT : GT_scope.

Definition powGT (a:GT) (b:Fp) : GT :=
  match a with | ConstrGT va =>
    ConstrGT (multFp va b)
  end
.
Infix "^" := powGT : GT_scope.

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
  pairing (i * a)%G1 b = ((pairing a b) ^ i)%GT.
Proof.
  intros.
  case a, b.
  unfold pairing, multG1, powGT.
  admit. (* TODO *)
Qed.

Theorem pairing_bilinear_r : forall (a:G1) (b:G2) (j:Fp),
  pairing a (j * b)%G2 = ((pairing a b) ^ j)%GT.
Proof.
  admit. (* TODO *)
Qed.

Theorem pairing_bilinear : forall (a:G1) (b:G2) (i j:Fp),
  pairing (i * a)%G1 (j * b)%G2 = ((pairing a b) ^ (i * j)%Fp)%GT.
Proof.
  admit. (* TODO *)
Qed.