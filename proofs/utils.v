(* NIZK Proof System - Useful functions by Remi Bazin *)




(* Imports *)
Require Import Arith.
Require Import NPeano.
Require Import Le.
Require Import List.




(* Various utils *)
Fixpoint repeat_fn (n:nat) (A:Type) (f:A -> A) (s:A) : A :=
  match n with
    | O => s
    | S m => repeat_fn m A f (f s)
  end
.

Lemma mod_S : forall (n p:nat), 2<=p -> ((S n) mod p=S (n mod p)) \/ ((S n) mod p=O).
Proof.
  admit. (* TODO *)
Qed.


Lemma rm_notin (A:Type) (l1 l2:list A) (x:A) (p:forall x y:A, {x = y} + {x <> y}) :
  (~In x l1) -> ((remove p x (l1++l2)) = l1++(remove p x l2)).
Proof.
  elim l1.
  (* Case l1=nil *)
    intro useless.
    rewrite (app_nil_l l2).
    rewrite (app_nil_l (remove p x l2)).
    reflexivity.
  (* Case l1 --> a::l1 *)
    intros a l Hrec xnotinal.
    assert (subg : ~ In x l).
    intro Hwrong.
    case (xnotinal (in_cons a x l Hwrong)).
    rewrite <- (app_comm_cons l l2 a).
    rewrite <- (app_comm_cons l (remove p x l2) a).
    rewrite <- (Hrec subg).
    unfold remove at 1.
    fold (remove p x (l++l2)).
    case (p x a).
    intro xisa.
    rewrite xisa in xnotinal.
    case (xnotinal (in_eq a l)).
    intro xisnota.
    reflexivity.
Qed.

Lemma nodup_rm (A:Type) (l:list A) (x:A) (p:forall x y:A, {x = y} + {x <> y}) :
  (NoDup l) -> ({~In x l} + {In x l /\ exists (l1 l2:list A),
    (l = l1++x::l2 /\ ~In x l1 /\ ~In x l2 /\ (remove p x l=l1++l2))}).
Proof.
  intros lnodup.
  case (in_dec p x l).
  (* Case In x l *)
    intro xinl.
    refine (right (conj xinl _)).
    destruct (in_split x l xinl).
    destruct H.
    refine (ex_intro _ x0 _).
    refine (ex_intro _ x1 _).
    rewrite H in lnodup.
    pose (subg := (NoDup_remove_2 x0 x1 x lnodup)).
    assert (xnotinx0 : ~In x x0).
    intro abs1.
    case (subg (in_or_app x0 x1 x (or_introl abs1))).
    assert (xnotinx1 : ~In x x1).
    intro abs2.
    case (subg (in_or_app x0 x1 x (or_intror abs2))).
    refine (conj H (conj xnotinx0 (conj xnotinx1 _))).
    rewrite H.
    rewrite (rm_notin A x0 (x::x1) x p xnotinx0).
    unfold remove.
    case (p x x).
    intro useless.
    fold (remove p x x1).
    rewrite <- (app_nil_r x1) at 1.
    rewrite (rm_notin A x1 nil x p xnotinx1).
    unfold remove.
    rewrite (app_assoc _ _ _).
    exact (app_nil_r _).
    intro Hwrong.
    case (Hwrong (eq_refl x)).
  (* Case ~In x l *)
    intro xnotinl.
    exact (left xnotinl).
Qed.

Lemma notin_rm (A:Type) (l:list A) (x:A) (p:forall x y:A, {x = y} + {x <> y}) :
  (~In x l) -> (remove p x l=l).
Proof.
  elim l.
  (* Case l=nil *)
    intro useless.
    unfold remove.
    reflexivity.
  (* Case l --> a::l *)
    intros.
    unfold remove.
    case (p x a).
    intro xisa.
    admit.
    intro xisnota.
    case (in_dec p x l0).
    intro xinl0.
    case (H0 (in_cons a x l0 xinl0)).
    intro xnotinl0.
    rewrite <- (H xnotinl0) at 2.
    reflexivity.
Qed.



(* Prime integer definition and properties *)
Definition Is_prime (n:nat) : Prop :=
  (2 <= n)
  /\
  (forall k:nat, (0<k<n) -> (NPeano.gcd k n = 1))
.

(* See https://www.eecs.northwestern.edu/~robby/courses/395-495-2013-fall/genrec_hw.v
   to prove the end of the recursion.
Print well_founded.
Print Acc.
Fixpoint mygcd (n m:nat) :=
  match le_lt_dec n m with
    | left _ => match n with
      | O => m
      | S O => 1
      | _ => mygcd n (m mod n)
    end
    | right _ => match m with
      | O => n
      | S O => 1
      | _ => mygcd (n mod m) m
    end
  end
.
*)

Lemma gcd_mult : forall (m n p:nat), m>0 -> n>0 -> p>0 ->
  gcd (m*n) p <= (gcd m p) * (gcd n p).
Proof.
  admit. (* TODO *)
Qed.




(* Mathematical structure properties *)
Definition Is_zero (G:Type) (add:G->G->G) (e:G) : Prop :=
  forall a:G, (add e a) = a
.
Definition Is_associative (G:Type) (add:G->G->G) : Prop :=
  forall (a b c:G), (add a (add b c)) = (add (add a b) c)
.
Definition Is_commutative (G:Type) (add:G->G->G) : Prop :=
  forall (a b:G), (add a b) = (add b a)
.
Definition Has_inverse (G:Type) (add:G->G->G) (e:G) : Prop :=
  (Is_zero G add e)
  /\
  (forall a:G, exists (b:G), (add a b) = e)
.
Definition Order_atmost_p (G:Type) (add:G->G->G) (e:G) (p:nat) : Prop :=
  (Is_zero G add e)
  /\
  (forall a:G, (repeat_fn p G (fun x => add x a) e) = e)
.

Definition Order_atleast_p (G:Type) (add:G->G->G) (e:G) (p:nat) : Prop :=
  (Is_zero G add e)
  /\
  (forall (a:G) (k:nat), 0<k<p -> a<>e -> (repeat_fn k G (fun x => add x a) e) <> e)
.

Definition Has_card (G:Type) (p:nat) : Prop :=
  (* At least p *)
  (exists l1:list G, ((length l1)=p) /\ (NoDup l1))
  /\
  (* At most p *)
  (~(exists l2:list G, ((length l2)>p) /\ (NoDup l2)))
.

(* Definition of an abelian group that is isomorphic to Fp *)
Definition Is_Fp_isomorphic (G:Type) (add:G->G->G) (p:nat) : Prop :=
  exists (e:G), (
    (* Note: Closure comes from the type of add. *)
    (* Associativity *)
    (Is_associative G add)
    /\
    (* Commutativity *)
    (Is_commutative G add)
    /\
    (* Identity element *)
    (Is_zero G add e)
    /\
    (* Inverse element *)
    (Has_inverse G add e)
    /\
    (* Prime order *)
    (Is_prime p)
    /\
    (* Order at most p *)
    (Order_atmost_p G add e p)
    /\
    (* Order at least p *)
    (Order_atleast_p G add e p)
    /\
    (* Cardinal check *)
    (Has_card G p)
  )
.
