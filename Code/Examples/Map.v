Require Import Lia.
Require Import Prelude.Orders.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
Require Import Interpretation.WeaklyMonotonicAlgebra.
Require Import Interpretation.Polynomial.
Require Import Interpretation.OrderInterpretation.

Local Open Scope nat.

Inductive base_types : Type :=
| TBtype : base_types
| TList  : base_types.

Definition Btype : ty base_types := Base TBtype.
Definition List : ty base_types := Base TList.

Inductive fun_symbols : Type :=
| TNil   : fun_symbols
| TCons  : fun_symbols
| TMap   : fun_symbols.

Definition map_ar
           (f : fun_symbols)
  : ty base_types
  := match f with
     | TNil   => List
     | TCons  => Btype ⟶ List ⟶ List
     | TMap   => (Btype ⟶ Btype) ⟶ List ⟶ List
     end.

Definition Nil
           {C : con base_types}
  : tm map_ar C List
  := BaseTm TNil.

Definition Cons
           {C : con base_types}
           (x : tm map_ar C Btype)
           (xs : tm map_ar C List)
  : tm map_ar C List
  := BaseTm TCons · x · xs.

Definition Map
           {C : con base_types}
           (f : tm map_ar C (Btype ⟶ Btype))
           (xs : tm map_ar C List)
  : tm map_ar C List
  := BaseTm TMap · f · xs.

Definition map_nil
  : rewriteRule map_ar
  := make_rewrite
       ((Btype ⟶ Btype) ,, ∙)
       List
       (let f := TmVar Vz in
        Map f Nil)
       Nil.

Definition map_cons
  : rewriteRule map_ar
  := make_rewrite
       ((Btype ⟶ Btype) ,, Btype ,, List ,, ∙)
       List
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        Map f (Cons x xs))
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        Cons (f · x) (Map f xs)).

Definition map_afs
  : afs base_types fun_symbols
  := make_afs
       map_ar
       (map_nil :: map_cons :: nil).

Open Scope poly_scope.

Definition map_fun_poly
           (f : fun_symbols)
  : poly ∙ (arity map_afs f)
  := match f with
     | TNil =>
       P_base (P_const 2)
     | TCons =>
       λP
       let y0 := P_var Vz in
       λP
       let y1 := P_var (Vs Vz) in
       P_base (P_const 3 +P from_poly y0 +P from_poly y1)
     | TMap =>
       λP
       let y0 := P_var Vz in
       λP
       let G1 := P_var (Vs Vz) in
       P_base (P_const 3
              +P (P_const 3) *P (from_poly y0)
              +P from_poly (G1 ·P P_base (from_poly y0))
              +P (P_const 3) *P (from_poly y0) *P from_poly (G1 ·P P_base (from_poly y0)))
     end.

Definition koe
           {n1 n2 m1 m2 : nat}
           (p : n1 = n2)
           (q : n2 > m2)
           (r : m1 = m2)
  : n1 > m1.
nia.
Qed.

Definition map_isSN
  : isSN map_afs.
Proof.
  apply afs_is_SN_from_Alg.
  simple refine (poly_WMalgebra _ _ _).
  - exact map_fun_poly.
  - intros r x.
    destruct r as [ r Hr ].
    repeat (destruct Hr as [ | Hr ]) ; try subst ; cbn -[Nat.add Nat.mul].
    + nia.
    + rewrite !PeanoNat.Nat.mul_0_l.
      rewrite !plus_O_n.
      rewrite <- !plus_n_O.
      induction x as [ f [ y0 [ y1 [] ]]].
      cbn -[Nat.add Nat.mul].

      (*
      assert (f (3 + y0 + (3 + y0) + y1 + (y1 + (3 + y0) + (3 + y1 + y0))) >= f y1).
      {
        apply f.
        cbn.
        nia.
      }
      assert (f (3 + y0 + (3 + y0) + y1 + (y1 + (3 + y0) + (3 + y1 + y0))) >= f y0).
      {
        apply f.
        cbn.
        nia.
      }
      assert (f (3 + y0 + (3 + y0) + y1 + (y1 + (3 + y0) + (3 + y1 + y0))) >= f 0).
      {
        apply f.
        cbn.
        nia.
      }
      nia.
       *)
      
      assert (f(4*y0 + 3*y1 + 12) >= f y1).
      {
        apply f.
        cbn.
        nia.
      }
      assert (f(4*y0 + 3*y1 + 12) >= f y0).
      {
        apply f.
        cbn.
        nia.
      }
      assert (f(4*y0 + 3*y1 + 12) >= f 0).
      {
        apply f.
        cbn.
        nia.
      }
      
      enough (36 * f(4*y0 + 3*y1 + 12)
              + 9 * y1 * f(4*y0 + 3*y1 + 12)
              + 12 * y0 * f(4*y0 + 3*y1 + 12)
              + f(4*y0 + 3*y1 + 12)
              + 3*(f 0)
              + 20*y0
              + 15*y1
              + 72
              >
              9*y1*f(y1)
              + 4*(f y0)
              + 3*(f y1)
              + 13*(f 0)
              + 4*y0
              + 15*y1
              + 48).
      {
        refine (koe _ H2 _) ; nia.

      }
      nia.
      
      nia.
        - nia.
        apply koe.
        Search (_ > _).
        admit.
      }
      nia.
        nia.

      assert (f (3 + y0 + (3 + y0) + y1 + (y1 + (3 + y0) + (3 + y1 + y0))) >= f y0).
      {
        apply f ; cbn.
        nia.
      }
      assert (f (3 + y0 + (3 + y0) + y1 + (y1 + (3 + y0) + (3 + y1 + y0))) >= f y1).
      {
        apply f ; cbn.
        nia.
      }
      assert (forall (z : nat), f z >= f 0).
      {
        intro.
        apply f ; cbn.
        nia.
      }
      nia.
      
      f y0
        f y0
        nia.
      cbn.
      Check fst x.
      Check snd x.
      rewrite !plus_O_n.
      admit.
    + destruct Hr.
Admitted.
