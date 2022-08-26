Require Import Syntax.Signature.

Inductive base_types : Type :=
| Nat   : base_types
| List  : base_types.

Inductive fun_symbols : Type :=
| Zero  : fun_symbols
| Succ  : fun_symbols
| Nil   : fun_symbols
| Cons  : fun_symbols
| App   : fun_symbols.

Definition app_ar
           (f : fun_symbols)
  : ty base_types
  := match f with
     | Zero  => Base Nat
     | Succ  => Base Nat ⟶ Base Nat
     | Nil   => Base List
     | Cons  => Base Nat ⟶ Base List ⟶ Base List
     | App   => Base List ⟶ Base List ⟶ Base List
     end.

Definition app_nil
  : rewriteRule app_ar
  := make_rewrite
       (Base List ,, ∙)
       (Base List)
       (let ys := TmVar Vz in
        (BaseTm App : tm app_ar _ _) · BaseTm Nil · ys)
       (let ys := TmVar Vz in
        ys).

Definition app_cons
  : rewriteRule app_ar
  := make_rewrite
       (Base List ,, Base Nat ,, Base List ,, ∙)
       (Base List)
       (let ys := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        BaseTm App · (BaseTm Cons · x · xs) · ys)
       (let ys := TmVar Vz in
        let x := TmVar (Vs Vz) in
        let xs := TmVar (Vs (Vs Vz)) in
        BaseTm Cons · x · (BaseTm App · xs · ys)).

Definition app_afs
  : afs base_types fun_symbols
  := make_afs
       app_ar
       (app_nil :: app_cons :: nil).
