Require Import Lia.
Require Import PeanoNat.
Import Nat.
Require Import List.
Require Import Prelude.Basics.
Require Import Prelude.Orders.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
Require Import Interpretation.WeaklyMonotonicAlgebra.
Require Import Interpretation.Polynomial.
Require Import Interpretation.PolynomialTactics.
Require Import Interpretation.PolynomialNotation.

Open Scope poly_scope.

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
       P_base (P_const 3 +P y0 +P y1)
     | TMap =>
       λP
       let y0 := P_var Vz in
       λP
       let G1 := P_var (Vs Vz) in
       P_base (P_const 3
              +P (P_const 3) *P y0
              +P G1 ·P from_poly y0
              +P (P_const 3) *P y0 *P G1 ·P from_poly y0)
     end.

Definition map_isSN
  : isSN map_afs.
Proof.
  apply afs_is_SN_from_Alg.
  apply (poly_WMalgebra _ map_fun_poly).
  solve_poly.
Qed.
