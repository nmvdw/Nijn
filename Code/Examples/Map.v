Require Import Nijn.Nijn.

Open Scope poly_scope.

(** The base types *)
Inductive base_types :=
| TBtype
| TList.

Global Instance decEq_base_types : decEq base_types.
Proof.
  decEq_finite.
Defined.

Definition Btype := Base TBtype.
Definition List := Base TList.

(** The function symbols and their arities *)
Inductive fun_symbols :=
| TNil
| TCons
| TMap.

Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
  decEq_finite.
Defined.

Definition map_ar f
  := match f with
     | TNil => List
     | TCons => Btype ⟶ List ⟶ List
     | TMap => (Btype ⟶ Btype) ⟶ List ⟶ List
     end.

Definition Nil {C} : tm map_ar C _ := BaseTm TNil.
Definition Cons {C} : tm map_ar C _ := BaseTm TCons.
Definition Map {C} : tm map_ar C _ := BaseTm TMap.

(** The rewrite rules *)
Program Definition map_nil :=
  make_rewrite
    (_ ,, ∙) _
    (Map · v_idx 0 _ · Nil)
    Nil.

Program Definition map_cons :=
  make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (Map · v_idx 0 _ · (Cons · v_idx 1 _ · v_idx 2 _))
    (Cons · (v_idx 0 _ · v_idx 1 _) · (Map · v_idx 0 _ · v_idx 2 _)).

(** The AFS *)
Definition map_afs :=
  make_afs
    map_ar
    (map_nil :: map_cons :: nil).

(** The polynomials *)
Definition map_fun_poly f : poly ∙ (arity map_afs f) :=
  match f with
  | TNil => P_base (P_const 2)
  | TCons =>
    λP let y0 := P_var Vz in
    λP let y1 := P_var (Vs Vz) in
    P_base (P_const 3 + y0 + y1)
  | TMap =>
    λP let y0 := P_var Vz in
    λP let G1 := P_var (Vs Vz) in
    P_base (P_const 3 + P_const 3 * y0 + G1 ·P y0 + P_const 3 * y0 * G1 ·P y0)
  end.

(** Strong normalization *)
Definition map_isSN : isSN map_afs.
Proof.
  solve_poly map_fun_poly.
Qed.
