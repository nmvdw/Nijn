Require Import Prelude.All.
Require Import Syntax.Signature.Kinds.

Open Scope signature.

(**
Type context
 *)
Inductive TyCon : Type :=
| empty : TyCon
| extend : TyCon -> TyCon.

Notation "'∙'" := empty : signature.
Notation "'⋆,,' Γ" := (extend Γ) (at level 70) : signature.

(**
Variables in a type context (De Bruijn indices)
 *)
Inductive TyVar : TyCon -> Type :=
| TyVz : forall {Γ : TyCon}, TyVar (⋆,, Γ)
| TyVs : forall {Γ : TyCon}, TyVar Γ -> TyVar (⋆,, Γ).
