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

Remark Fp_equality2 : forall (n1 n2:nat), Fp_from_nat n1=Fp_from_nat n2 -> n1 mod p=n2 mod p.
Proof.
  intros.
  unfold Fp_from_nat in H.
  inversion H.
  reflexivity.
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

Lemma repeated_addition_Fp : forall (x:nat) (l:x<p) (k m:nat),
    repeat_fn k Fp (fun x0 : Fp => addFp x0 (ConstrFp x l)) (Fp_from_nat m)
    = Fp_from_nat (k * x + m).
Proof.
  intros x l k.
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
Qed.

Theorem Fp_order_atmost_p : Order_atmost_p Fp addFp Fp_0 p.
Proof.
  unfold Order_atmost_p.
  refine (conj Fp_0_well_formed _).
  intros.
  case a.
  intros.
  pose (result := repeated_addition_Fp x l p O).
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
  unfold Order_atleast_p.
  refine (conj Fp_0_well_formed _).
  intros.
  destruct a.
  assert (fp0 : Fp_0 = Fp_from_nat O).
  unfold Fp_0, Fp_from_nat.
  exact (Fp_equality _ _ _ _ (eq_sym (Nat.mod_0_l p p_is_not_null))).
  rewrite fp0.
  intros.
  rewrite (repeated_addition_Fp x l k O).
  unfold Fp_from_nat.
  intro wrong.
  inversion wrong.
  rewrite (Nat.mod_0_l p p_is_not_null) in H2.
  rewrite <- (plus_n_O (k*x)) in H2.
  pose (equiv := Nat.mod_divides (k*x) p p_is_not_null).
  inversion equiv.
  pose (H4 := H1 H2).
  inversion H4.
  pose (Hk := (proj2 p_prime) k H).
  assert (subg : O <> x).
  intro Hfalse.
  unfold Fp_0 in H0.
  case (H0 (Fp_equality _ _ _ _ (eq_sym Hfalse))).
  pose (Hx := (proj2 p_prime) x (conj (neq_0_lt x subg) l)).
  pose (gcdeq := gcd_mult k x p (proj1 H) (neq_0_lt x subg) (neq_0_lt p (not_eq_sym p_is_not_null))).
  rewrite H5, Hk, Hx in gcdeq.
  simpl in gcdeq.
  rewrite (Nat.gcd_comm (p*x0) p) in gcdeq.
  rewrite (Nat.gcd_mul_diag_l p x0 (le_0_n p)) in gcdeq.
  pose (wrong2 := le_trans 2 p 1 (proj1 p_prime) gcdeq).
  case (le_Sn_n 1 wrong2).
Qed.

Fixpoint Fp_lst_increasing (n:nat) : list Fp :=
  match n with
    | O => nil
    | S m => cons (Fp_from_nat m) (Fp_lst_increasing m)
  end
.


Theorem Fp_card : Has_card Fp p.
Proof.
  unfold Has_card.
  refine (conj _ _).
  (* Part 1: Cardinal at least p *)
  refine (ex_intro _ (Fp_lst_increasing p) _).
  refine (conj _ _).
    (* Correct list length *)
    elim p.
    unfold Fp_lst_increasing, length.
    reflexivity.
    intros.
    assert (subg : S (length (Fp_lst_increasing n)) = S n).
    rewrite H.
    reflexivity.
    unfold Fp_lst_increasing, length.
    exact subg.
    (* No duplicates *)
    assert (mainsubg : forall i:nat, i<=p -> NoDup (Fp_lst_increasing i)).
    intro.
    elim i.
    intro useless.
    unfold Fp_lst_increasing.
    constructor.
    intros n recc.
    assert (subg : S n <= p -> NoDup (cons (Fp_from_nat n) (Fp_lst_increasing n))).
    assert (subg2 : S n <= p -> ~ In (Fp_from_nat n) (Fp_lst_increasing n)).
    elim n.
    intro useless.
    unfold Fp_lst_increasing.
    simpl.
    intro.
    case H.
    intros.
    assert (subg : ~ In (Fp_from_nat (S n0)) (cons (Fp_from_nat n0) (Fp_lst_increasing n0))).
    intro.
    destruct H1.
    unfold Fp_from_nat in H1.
    inversion H1.
    pose (H4 := mod_S n0 p (proj1 p_prime)).
    destruct H4.
    rewrite H2 in H3.
    case (n_Sn (n0 mod p) H3).
    rewrite H2 in H3.
    pose (H4 := proj1 (Nat.mod_divides n0 p p_is_not_null) H3).
    destruct H4.
    rewrite H4 in H2.
    rewrite <- (plus_O_n (S (p * x))) in H2.
    rewrite <- (plus_Snm_nSm O (p*x)) in H2.
    rewrite (mult_comm p x) in H2.
    rewrite (Nat.mod_add 1 x p p_is_not_null) in H2.
    rewrite (Nat.mod_small 1 p (proj1 p_prime)) in H2.
    discriminate H2.
    assert (myind : forall k:nat, k<=n0 -> ~In (Fp_from_nat (S n0)) (Fp_lst_increasing k)).
    intro.
    elim k.
    intro useless.
    unfold Fp_lst_increasing.
    exact (in_nil (a:=Fp_from_nat (S n0))).
    intros.
    assert (subg3 : ~ ((Fp_from_nat n1=Fp_from_nat (S n0)) \/
      (In (Fp_from_nat (S n0)) (Fp_lst_increasing n1)))).
    intro wrong1.
    destruct wrong1.
    pose (H5 := Fp_equality2 n1 (S n0) H4).
    rewrite (Nat.mod_small (S n0) p H0) in H5.
    rewrite (Nat.mod_small n1 p (le_trans (S n1) n0 p H3
      (le_Sn_le n0 p (le_Sn_le (S n0) p H0)):S n1<=p)) in H5.
    rewrite H5 in H3.
    case (le_Sn_n (S n0) (le_S (S (S n0)) n0 H3)).
    case (H2 (le_Sn_le n1 n0 H3) H4).
    unfold Fp_lst_increasing, In.
    exact subg3.
    case (myind n0 (le_n n0) H1).
    unfold Fp_lst_increasing.
    exact subg.
    intro cond.
    exact (NoDup_cons (A:=Fp) (Fp_from_nat n) (l:=Fp_lst_increasing n)
      (subg2 cond) (recc (le_Sn_le n p cond))).
    unfold Fp_lst_increasing.
    exact subg.
    exact (mainsubg p (le_n p)).
  (* Part 2: Cardinal at most p *)
  assert (subg : forall k:nat, k<=p -> ~(exists l:list Fp, length l > k /\ NoDup l /\
    (forall e:nat, e<p -> e>=k -> ~ In (Fp_from_nat e) l))).
  intro.
  elim k.
  admit. (* TODO *)
  admit. (* TODO *)
  pose (test := subg p (le_n p)).
  intro.
  assert (subg2 : exists l : list Fp,
          length l > p /\
          NoDup l /\
          (forall e : nat, e < p -> e >= p -> ~ In (Fp_from_nat e) l)).
  destruct H.
  destruct H.
  refine (ex_intro _ x _).
  refine (conj _ (conj _ _)).
  exact H.
  exact H0.
  intros.
  unfold ge in H2.
  case (le_not_lt p e H2 H1).
  case (test subg2).
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

Lemma Fp_plus_n_O : forall n, n = n+Fp_0.
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

Lemma Fp_plus_O_n : forall n, Fp_0+n = n.
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

Lemma Fp_plus_comm : forall n m, n+m = m+n.
Proof.
  intros.
  case n, m.
  unfold addFp.
  assert (subg : (x+x0) mod p = (x0+x) mod p).
  rewrite (plus_comm x x0).
  reflexivity.
  exact (Fp_equality _ _ _ _ subg).
Qed.

Lemma Fp_plus_assoc : forall n m p, n+(m+p) = n+m+p.
Proof.
  intros.
  case n, m, p0.
  unfold addFp.
  assert (subg : (x + (x0 + x1) mod p) mod p = ((x + x0) mod p + x1) mod p).
  rewrite (Nat.add_mod_idemp_r x (x0+x1) p p_is_not_null).
  rewrite (Nat.add_mod_idemp_l (x+x0) x1 p p_is_not_null).
  rewrite (plus_assoc x x0 x1).
  reflexivity.
  exact (Fp_equality _ _ _ _ subg).
Qed.

Lemma Fp_plus_permute : forall n m p, n + (m + p) = m + (n + p).
Proof.
  intros.
  case n, m, p0.
  unfold addFp.
  refine (Fp_equality _ _ _ _ _).
  rewrite (Nat.add_mod_idemp_r x (x0+x1) p p_is_not_null).
  rewrite (Nat.add_mod_idemp_r x0 (x+x1) p p_is_not_null).
  rewrite (plus_permute x x0 x1).
  reflexivity.
Qed.

Lemma Fp_plus_assoc_reverse : forall n m p, n + m + p = n + (m + p).
Proof.
  intros.
  case n, m, p0.
  unfold addFp.
  refine (Fp_equality _ _ _ _ _).
  rewrite (Nat.add_mod_idemp_r x (x0+x1) p p_is_not_null).
  rewrite (Nat.add_mod_idemp_l (x+x0) x1 p p_is_not_null).
  rewrite (plus_assoc x x0 x1).
  reflexivity.
Qed.

Lemma Fp_plus_reg_l : forall n m p, p + n = p + m -> n = m.
Proof.
  admit.
Qed.

Lemma Fp_n_Sn : forall n, n <> n + Fp_1.
Proof.
  intro.
  destruct n.
  unfold Fp_1, addFp.
  intro wrong.
  inversion wrong.
  pose (tmp := mod_S x p (proj1 p_prime)).
  rewrite (plus_n_O (S x)) in tmp.
  rewrite (plus_Snm_nSm x O) in tmp.
  destruct tmp.
  rewrite H in H0.
  rewrite (Nat.mod_small x p l) in H0.
  case (n_Sn x H0).
  pose (tmp := proj1 (Nat.mod_divides (x+1) p p_is_not_null) H).
  destruct tmp.
  case_eq x0.
  intro wrong2.
  rewrite wrong2 in H1.
  rewrite (mult_0_r p) in H1.
  discriminate (proj2 (plus_is_O x 1 H1)).
  intros.
  case_eq n.
  admit.
  intros.
  rewrite H2 in H1.
  rewrite (mult_succ_r p n) in H1.
  rewrite H3 in H1.
  rewrite (mult_succ_r p n0) in H1.
  pose (l2 := l).
  unfold lt in l2.
  rewrite (plus_n_O (S x)) in l2.
  rewrite (plus_Snm_nSm x O) in l2.
  rewrite H1 in l2.
  rewrite (plus_comm (p * n0 + p) p) in l2.
  rewrite (plus_n_O p) in l2 at 4.
  pose (l3 := le_trans (p*n0+p) O (p*n0) (plus_le_reg_l (p*n0+p) O p l2) (le_0_n (p*n0))).
  rewrite (plus_n_O (p*n0)) in l3 at 2.
  pose (l4 := le_n_0_eq p (plus_le_reg_l p O (p*n0) l3)).
  case (p_is_not_null (eq_sym l4)).
Qed.

Lemma Fp_plus_le_reg_l : forall n m p, p + n <= p + m -> n <= m.
Proof.
  admit.
Qed.

Lemma Fp_plus_le_reg_l : forall n m p, p + n <= p + m -> n <= m.
Proof.
  admit.
Qed.

Lemma Fp_plus_le_reg_l : forall n m p, p + n <= p + m -> n <= m.
Proof.
  admit.
Qed.

Lemma Fp_plus_le_reg_l : forall n m p, p + n <= p + m -> n <= m.
Proof.
  admit.
Qed.

Lemma Fp_plus_le_reg_l : forall n m p, p + n <= p + m -> n <= m.
Proof.
  admit.
Qed.

Lemma Fp_plus_le_reg_l : forall n m p, p + n <= p + m -> n <= m.
Proof.
  admit.
Qed.

Close Scope Fp_scope.
