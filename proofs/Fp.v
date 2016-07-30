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

Delimit Scope Fp_scope with Fp.

Definition Fp_0 : Fp :=
  ConstrFp 0 (le_trans 1 2 p (le_S 1 1 (le_n 1)) p_big).
Definition Fp_1 : Fp := ConstrFp 1 p_big.

Definition Fp_from_nat (n:nat) : Fp :=
  ConstrFp (n mod p) (Nat.mod_upper_bound n p p_is_not_null).

Definition addFp (a b:Fp) : Fp :=
  match a with | ConstrFp v_a p_a =>
    match b with | ConstrFp v_b p_b =>
      ConstrFp ((v_a + v_b) mod p) (Nat.mod_upper_bound (v_a + v_b) p p_is_not_null)
    end
  end
.
Infix "+" := addFp : Fp_scope.

Definition succFp (a:Fp) : Fp := addFp a Fp_1.

Definition multFp (a b:Fp) : Fp :=
  match a with | ConstrFp v_a p_a =>
    match b with | ConstrFp v_b p_b =>
      ConstrFp ((v_a * v_b) mod p) (Nat.mod_upper_bound (v_a * v_b) p p_is_not_null)
    end
  end
.
Infix "*" := multFp : Fp_scope.




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
  intros.
  destruct a.
  rewrite (plus_O_n x).
  assert (part1 : (x mod p) = x).
    exact (Nat.mod_small x p l).
  exact (Fp_equality (x mod p) x (Nat.mod_upper_bound x p p_is_not_null) l part1).
Qed.

Theorem Fp_associative : Is_associative Fp addFp.
Proof.
  unfold Is_associative.
  intros.
  case a, b, c.
  unfold addFp.
  assert (subg : (x + (x0 + x1) mod p) mod p = ((x + x0) mod p + x1) mod p).
  rewrite (Nat.add_mod_idemp_r x (x0 + x1) p p_is_not_null).
  rewrite (Nat.add_mod_idemp_l (x + x0) x1 p p_is_not_null).
  rewrite (plus_assoc x x0 x1).
  reflexivity.
  exact (Fp_equality _ _ _ _ subg).
Qed.

Theorem Fp_commutative : Is_commutative Fp addFp.
Proof.
  unfold Is_commutative.
  intros.
  case a, b.
  unfold addFp.
  assert (subg : (x + x0) mod p = (x0 + x) mod p).
  rewrite (plus_comm x x0).
  reflexivity.
  exact (Fp_equality _ _ _ _ subg).
Qed.

Theorem Fp_has_inverse : Has_inverse Fp addFp Fp_0.
Proof.
  unfold Has_inverse.
  refine (conj Fp_0_well_formed _).
  intros.
  case a.
  intros.
  refine (ex_intro _ (ConstrFp ((p-x) mod p) (Nat.mod_upper_bound _ p p_is_not_null)) _).
  unfold Fp_0, addFp.
  assert (subg : (x + (p - x) mod p) mod p = 0).
  rewrite (Nat.add_mod_idemp_r x (p-x) p p_is_not_null).
  rewrite <- (le_plus_minus x p (le_S_n x p (le_S (S x) p l))).
  exact (Nat.mod_same p p_is_not_null).
  exact (Fp_equality _ _ _ _ subg).
Qed.

Theorem Fp_order_atmost_p : Order_atmost_p Fp addFp Fp_0 p.
Proof.
  unfold Order_atmost_p.
  refine (conj Fp_0_well_formed _).
  intros.
  case a.
  intros.
  assert (generalization : forall (k m:nat),
    repeat_fn k Fp (fun x0 : Fp => addFp x0 (ConstrFp x l)) (Fp_from_nat m)
    = Fp_from_nat (k * x + m)).
  (* Generalization proof *)
  intro.
  elim k.
    (* Case k=0 *)
    rewrite (mult_0_l x).
    intro.
    rewrite (plus_O_n m).
    unfold repeat_fn, Fp_0, Fp_from_nat.
    reflexivity.
    (* Case k --> k+1 *)
    intros.
    assert (subg : repeat_fn n Fp (fun x0 : Fp => addFp x0 (ConstrFp x l))
      (addFp (Fp_from_nat m) (ConstrFp x l))
      = Fp_from_nat (S n * x + m)).
    assert (left : addFp (Fp_from_nat m) (ConstrFp x l) = Fp_from_nat (x+m)).
    unfold Fp_from_nat, addFp.
    assert (tmp : (m mod p + x) mod p = (x + m) mod p).
    rewrite (Nat.add_mod_idemp_l m x p p_is_not_null).
    rewrite (plus_comm x m).
    reflexivity.
    exact (Fp_equality _ _ _ _ tmp).
    assert (right : (S n) * x + m = n * x + (x+m)).
    rewrite (mult_succ_l n x).
    rewrite (plus_assoc (n*x) x m).
    reflexivity.
    rewrite left.
    rewrite right.
    exact (H (x+m)).
    unfold repeat_fn.
    exact subg.
  (* Back to specialized case *)
  pose (result := generalization p O).
  rewrite <- (plus_n_O (p*x)) in result.
  assert (subg1 : Fp_from_nat (x * p) = Fp_0).
  unfold Fp_from_nat, Fp_0.
  assert (subg2 : (x*p) mod p=0).
  rewrite (Nat.mod_mul x p p_is_not_null).
  reflexivity.
  exact (Fp_equality _ _ _ _ subg2).
  assert (subg3 : Fp_from_nat O = Fp_0).
  unfold Fp_from_nat, Fp_0.
  assert (subg4 : 0 mod p = 0).
  rewrite (Nat.mod_0_l p p_is_not_null).
  reflexivity.
  exact (Fp_equality _ _ _ _ subg4).
  rewrite (mult_comm p x) in result.
  rewrite subg1 in result.
  rewrite subg3 in result.
  exact result.
Qed.

Theorem Fp_order_atleast_p : Order_atleast_p Fp addFp Fp_0 p.
Proof.
  admit. (* TODO *)
Qed.

Theorem Fp_card : Has_card Fp p.
Proof.
  admit. (* TODO *)
Qed.

Theorem Fp_well_formed : Is_Fp_isomorphic Fp addFp p.
Proof.
  unfold Is_Fp_isomorphic.
  refine (ex_intro _ Fp_0 _).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
  exact Fp_associative.
  exact Fp_commutative.
  exact Fp_0_well_formed.
  exact Fp_has_inverse.
  exact p_prime.
  exact Fp_order_atmost_p.
  exact Fp_order_atleast_p.
  exact Fp_card.
Qed.




(* Utility properties inspired from the nat library *)
Open Scope Fp_scope.

Lemma Fp_plus_n_O : forall n:Fp, n = n+Fp_0.
Proof.
  intro.
  case n.
  intros.
  unfold Fp_0, addFp.
  assert (subg : x = (x+0) mod p).
  rewrite <- (plus_n_O x).
  exact (eq_sym (Nat.mod_small x p l)).
  exact (Fp_equality _ _ _ _ subg).
Qed.

Lemma Fp_plus_O_n : forall n:Fp, Fp_0+n = n.
Proof.
  intro.
  case n.
  intros.
  unfold Fp_0, addFp.
  assert (subg : (0+x) mod p = x).
  rewrite (plus_O_n x).
  exact (Nat.mod_small x p l).
  exact (Fp_equality _ _ _ _ subg).
Qed.

Lemma Fp_plus_comm : forall (n m:Fp), n+m = m+n.
Proof.
  intros.
  case n, m.
  unfold addFp.
  assert (subg : (x+x0) mod p = (x0+x) mod p).
  rewrite (plus_comm x x0).
  reflexivity.
  exact (Fp_equality _ _ _ _ subg).
Qed.

Close Scope Fp_scope.
