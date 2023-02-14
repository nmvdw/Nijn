Require Import Nijn.Nijn.
Open Scope poly_scope.

Inductive base_types := 
| Ca  
| Clist.

Global Instance decEq_base_types : decEq base_types.
Proof.
  decEq_finite.
Defined.


Definition a := Base Ca.
Definition list := Base Clist.

Inductive fun_symbols := 
| Tcons  
| Tmap  
| Tnil.

Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
  decEq_finite.
Defined.


Definition fn_arity fn_symbols := 
  match fn_symbols with
  | Tcons  =>  a ⟶ list ⟶ list
  | Tmap  =>  list ⟶ (a ⟶ a) ⟶ list
  | Tnil => list
  end.

Definition cons {C} : tm fn_arity C _ := BaseTm Tcons.
Definition map {C} : tm fn_arity C _ := BaseTm Tmap.
Definition nil {C} : tm fn_arity C _ := BaseTm Tnil.

Program Definition rule_0 := 
  make_rewrite
    (_ ,, ∙) _
    (map · nil ·  V 0)
    nil.

Program Definition rule_1 := 
  make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (map · (cons ·  V 0 ·  V 1) ·  V 2)
    (cons · ( V 2 ·  V 0) · (map ·  V 1 ·  V 2)).

Definition trs := 
  make_afs
    fn_arity 
    (rule_0 :: rule_1 :: List.nil).

Definition map_fun_poly fn_symbols : poly ∙ (arity trs fn_symbols) := 
  match fn_symbols with
  | Tnil => to_Poly (P_const 3)
  | Tcons  => λP λP let y1 := P_var Vz in
    to_Poly (P_const 3
             + P_const 2 * y1)
  | Tmap  =>  λP let y0 := P_var (Vs Vz) in λP let G1 := P_var Vz in
    to_Poly (P_const 3 * y0
             + P_const 3 * y0 * (G1 ·P (y0)))
  end.

Definition  trs_isSN : isSN trs.
Proof.
  solve_poly_SN map_fun_poly.
Qed.
