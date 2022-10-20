Require Import Nijn.

Open Scope poly_scope.

(** The base types *)
Inductive base_types := TBtype | TList.

Definition Btype : ty base_types := Base TBtype.
Definition List : ty base_types := Base TList.

(** The function symbols and their arities *)
Inductive fun_symbols := TNil | TCons | TMap.

Definition map_ar
           (f : fun_symbols)
  : ty base_types
  := match f with
     | TNil   => List
     | TCons  => Btype ⟶ List ⟶ List
     | TMap   => (Btype ⟶ Btype) ⟶ List ⟶ List
     end.

Definition Nil {C}
  : tm map_ar C List
  := BaseTm TNil.

Definition Cons {C} x xs
  : tm map_ar C List
  := BaseTm TCons · x · xs.

Definition Map {C} f xs
  : tm map_ar C List
  := BaseTm TMap · f · xs.

(** The rewrite rules *)
Definition map_nil
  : rewriteRule map_ar
  := make_rewrite
       (_ ,, ∙)
       _
       (let f := TmVar Vz in
        Map f Nil)
       Nil.

Definition map_cons
  : rewriteRule map_ar
  := make_rewrite
       (_ ,, _ ,, _ ,, ∙)
       _
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        Map f (Cons x xs))
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        Cons (f · x) (Map f xs)).

(** The AFS *)
Definition map_afs
  : afs base_types fun_symbols
  := make_afs
       map_ar
       (map_nil :: map_cons :: nil).

(** The polynomials *)
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
              +P P_const 3 *P y0
              +P G1 ·P y0
              +P P_const 3 *P y0 *P G1 ·P y0)
     end.

(** Strong normalization *)
Definition map_isSN
  : isSN map_afs.
Proof.
  apply afs_is_SN_from_Alg.
  apply (poly_WMalgebra _ map_fun_poly).
  solve_poly.
Qed.
