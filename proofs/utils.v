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
