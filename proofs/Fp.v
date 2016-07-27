(* NIZK Proof System - Field Fp = Z/pZ defintion and properties by Rémi Bazin *)

Load utils.




(* Primery group order *)
Variable p : nat.

Hypothesis p_prime : Is_prime p.

Lemma p_big : 2 <= p.
Proof.
  pose (p_prime := p_prime).
  unfold Is_prime in p_prime.
  inversion p_prime.
  exact H.
Qed.

Lemma p_is_not_null : p <> 0.
Proof.
  intro H.
  pose (p_big := p_big).
  rewrite H in p_big.
  pose (wrong := le_Sn_0 1 p_big).
  case wrong.
Qed.




(* Definition of Fp and its main elements *)
Inductive Fp : Set := | ConstrFp : forall x:nat, (x<p -> Fp).

Definition Fp_0 : Fp :=
  ConstrFp 0 (le_trans 1 2 p (le_S 1 1 (le_n 1)) p_big).
Definition Fp_1 : Fp := ConstrFp 1 p_big.

Definition addFp (a b:Fp) : Fp :=
  match a with | ConstrFp v_a p_a =>
    match b with | ConstrFp v_b p_b =>
      ConstrFp ((v_a + v_b) mod p) (Nat.mod_upper_bound (v_a + v_b) p p_is_not_null)
    end
  end
.

Definition succFp (a:Fp) : Fp := addFp a Fp_1.

Definition multFp (a b:Fp) : Fp :=
  match a with | ConstrFp v_a p_a =>
    match b with | ConstrFp v_b p_b =>
      ConstrFp ((v_a * v_b) mod p) (Nat.mod_upper_bound (v_a * v_b) p p_is_not_null)
    end
  end
.




(* Mathematical structure properties *)
Remark Fp_equality : forall (n1 n2:nat) (p1:n1<p) (p2:n2<p), n1=n2 -> ConstrFp n1 p1 = ConstrFp n2 p2.
Proof. (* Thanks to Cyprien Mangin for this proof! *)
  intros.
  subst.
  f_equal.
  apply le_unique.
Qed.

Theorem Fp_0_well_formed : Is_zero Fp addFp Fp_0.
Proof.
  unfold Is_zero, Fp_0, addFp.
  intro a.
  destruct a.
  rewrite (plus_O_n x).
  assert (part1 : (x mod p) = x).
    pose (p_pos := le_trans 1 2 p (le_S 1 1 (le_n 1)) p_big). (* TODO remove if not used *)
    pose (useful := mod_bound_pos x p (le_0_n x)
      (le_trans 1 2 p (le_S 1 1 (le_n 1)) p_big)).
    inversion useful.
    pose (eq := div_mod x p p_is_not_null).
    case_eq (x/p).
      (* Case x/p = 0 *)
      intro H1.
      rewrite H1 in eq.
      rewrite <- (mult_n_O p) in eq.
      unfold plus in eq.
      rewrite <- eq.
      reflexivity.
      (* Case x/p > 0 *)
      intros n H1.
      rewrite H1 in eq.
      rewrite <- (mult_n_Sm p n) in eq.
      assert (wrong1 : p * n + p + x mod p <= x).
      rewrite <- eq.
      exact (le_n x).
      rewrite <- (plus_assoc (p * n) p (x mod p)) in wrong1.
      rewrite (plus_permute (p * n) p (x mod p)) in wrong1.
      pose (wrong2 := le_trans p (p + (p * n + x mod p)) x
        (le_plus_l p (p*n + x mod p)) wrong1).
      case (lt_not_le x p l wrong2).
  exact (Fp_equality (x mod p) x (Nat.mod_upper_bound x p p_is_not_null) l part1).
Qed.
