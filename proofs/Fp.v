(* NIZK Proof System - Field Fp = Z/pZ defintion and properties *)

Load utils.




(* Primery group order *)
Variable p : nat.

Hypothesis p_big : 2 <= p.

Lemma p_is_not_null : p <> 0.
Proof.
  intro H.
  pose (p_big := p_big).
  rewrite H in p_big.
  pose (wrong := le_Sn_0 1 p_big).
  case wrong.
Qed.




(* Definition of Fp and its main elements *)
Inductive Fp : Set :=
  | ConstrFp : forall x:nat, (x<p -> Fp).

Definition Fp_0 : Fp :=
  ConstrFp 0 (le_trans 1 2 p (le_S 1 1 (le_n 1)) p_big).
Definition Fp_1 : Fp := ConstrFp 1 p_big.

Definition addFp (a b:Fp) : Fp :=
  match a with | ConstrFp v_a p_a =>
    match b with | ConstrFp v_b p_b =>
      ConstrFp (NPeano.modulo (v_a + v_b) p) (NPeano.Nat.mod_upper_bound (v_a + v_b) p p_is_not_null)
    end
  end
.

Definition succFp (a:Fp) : Fp := addFp a Fp_1.

Definition multFp (a b:Fp) : Fp :=
  match a with | ConstrFp v_a p_a =>
    match b with | ConstrFp v_b p_b =>
      ConstrFp (NPeano.modulo (v_a * v_b) p) (NPeano.Nat.mod_upper_bound (v_a * v_b) p p_is_not_null)
    end
  end
.
