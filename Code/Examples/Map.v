Require Import Syntax.Signature.

Inductive base_types : Type :=
| Nat   : base_types
| List  : base_types.

Inductive fun_symbols : Type :=
| Zero  : fun_symbols
| Succ  : fun_symbols
| Nil   : fun_symbols
| Cons  : fun_symbols
| Map   : fun_symbols.

Definition map_ar
           (f : fun_symbols)
  : ty base_types
  := match f with
     | Zero  => Base Nat
     | Succ  => Base Nat ⟶ Base Nat
     | Nil   => Base List
     | Cons  => Base Nat ⟶ Base List ⟶ Base List
     | Map   => (Base Nat ⟶ Base Nat) ⟶ Base List ⟶ Base List
     end.

Definition map_nil
  : rewriteRule map_ar
  := make_rewrite
       ((Base Nat ⟶ Base Nat) ,, ∙)
       (Base List)
       (let f := TmVar Vz in
        BaseTm Map · f · BaseTm Nil : tm map_ar _ _)
       (BaseTm Nil).

Definition map_cons
  : rewriteRule map_ar
  := make_rewrite
       ((Base Nat ⟶ Base Nat) ,, Base Nat ,, Base List ,, ∙)
       (Base List)
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        BaseTm Map · f · (BaseTm Cons · x · xs))
       (let f := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        BaseTm Cons · (f · x) · (BaseTm Map · f · xs)).

Definition map_afs
  : afs base_types fun_symbols
  := make_afs
       map_ar
       (map_nil :: map_cons :: nil).
