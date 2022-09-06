Require Import Prelude.CompatibleRelation.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
Require Import Interpretation.WeaklyMonotonicAlgebra.
Require Import Interpretation.Polynomial.
Require Import Interpretation.OrderInterpretation.

Local Open Scope nat.

Inductive base_types : Type :=
| TNat   : base_types
| TList  : base_types.

Definition Nat : ty base_types := Base TNat.
Definition List : ty base_types := Base TList.

Inductive fun_symbols : Type :=
| TZero  : fun_symbols
| TSucc  : fun_symbols
| TNil   : fun_symbols
| TCons  : fun_symbols
| TMap   : fun_symbols.

Definition map_ar
           (f : fun_symbols)
  : ty base_types
  := match f with
     | TZero  => Nat
     | TSucc  => Nat ⟶ Nat
     | TNil   => List
     | TCons  => Nat ⟶ List ⟶ List
     | TMap   => (Nat ⟶ Nat) ⟶ List ⟶ List
     end.

Definition Zero
           {C : con base_types}
  : tm map_ar C Nat
  := BaseTm TZero.

Definition Suc
           {C : con base_types}
  : tm map_ar C (Nat ⟶ Nat)
  := BaseTm TSucc.

Definition Nil
           {C : con base_types}
  : tm map_ar C List
  := BaseTm TNil.

Definition Cons
           {C : con base_types}
  : tm map_ar C (Nat ⟶ List ⟶ List)
  := BaseTm TCons.

Definition Map
           {C : con base_types}
  : tm map_ar C ((Nat ⟶ Nat) ⟶ List ⟶ List)
  := BaseTm TMap.

Definition map_nil
  : rewriteRule map_ar
  := make_rewrite
       ((Nat ⟶ Nat) ,, ∙)
       List
       (let f := TmVar Vz in
        Map · f · Nil)
       Nil.

Definition map_cons
  : rewriteRule map_ar
  := make_rewrite
       ((Nat ⟶ Nat) ,, Nat ,, List ,, ∙)
       List
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        Map · f · (Cons · x · xs))
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        Cons · (f · x) · (Map · f · xs)).

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
     | TZero =>
       P_base (P_const 1)
     | TSucc =>
       λP
       let x := P_var Vz in
       P_base (from_poly x +P P_const 1)
     | TNil =>
       P_base (P_const 1)
     | TCons =>
       λP
       let x := P_var Vz in
       λP
       let xs := P_var (Vs Vz) in
       P_base (P_const 1 +P (from_poly x +P from_poly xs))
     | TMap =>
       λP
       let xs := P_var Vz in
       λP
       let f := P_var (Vs Vz) in
       P_base (P_const 1 +P ((P_const 1 +P from_poly xs) *P from_poly (f ·P P_base (from_poly xs))))
     end.

Close Scope poly_scope.

(*
Notation "0" := (P_const 0).
Notation "1" := (P_const 1).
Notation "2" := (P_const 2).
Notation "3" := (P_const 3).

Definition map_fun_poly
  : forall f : fun_symbols, poly ∙ (arity map_afs f)
  := fun f =>
     match f with
     | TZero =>
       P_base 1
     | TSucc =>
       λP
       let x := P_var Vz in
       P_base (from_poly x +P 1)
     | TNil =>
       P_base 1
     | TCons =>
       λP
       let x := P_var Vz in
       λP
       let xs := P_var (Vs Vz) in
       P_base (1 +P (from_poly x +P from_poly xs))
     | TMap =>
       λP
       let xs := P_var Vz in
       λP
       let f := P_var (Vs Vz) in
       P_base (1 +P ((1 +P from_poly xs) *P from_poly (f ·P P_base (from_poly xs))))
     end.
 *)

(*
Definition map_isSN
  : isSN map_afs.
Proof.
  apply afs_is_SN_from_Alg.
  simple refine (poly_WMalgebra _ _ _ _ _ _ _).
  - exact map_fun_poly.
  - intros A1 A2.
    refine (P_app _ _).
    + apply P_var.
      apply Vz.
    + apply P_var.
      apply Vs.
      apply Vz.
  - intros A1 A2 f x.
    cbn.
    apply ge_refl.
  - intros A1 A2 f1 f2 x Hf.
    cbn.
    apply Hf.
  - intros A1 A2 f x1 x2 Hx.
    cbn.
    admit.
  - intros r x.
    cbn in *.
    destruct r as [ r Hr ].
    repeat (destruct Hr as [ | Hr ]) ; try subst ; cbn in *.
    + destruct x ; cbn in *.
      admit.
    + destruct x as [ f [ x1 [ x2 [ ] ] ] ].
      nia.
      admit.
    + contradiction.
Admitted.
 *)
