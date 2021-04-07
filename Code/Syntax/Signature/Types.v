Require Import Prelude.All.
Require Import Syntax.Signature.Kinds.
Require Import Syntax.Signature.TypeContexts.

Section Types.
  Context {baseTy : Type}
          (ar : baseTy -> Type).
  
  (** Monomorphic types *)
  Inductive MonTy : TyCon -> Type :=
  | Ty_var : forall (Γ : TyCon), TyVar Γ -> MonTy Γ
  | base : forall (Γ : TyCon) (b : baseTy), (ar b -> MonTy Γ) -> MonTy Γ
  | function : forall (Γ : TyCon), MonTy Γ -> MonTy Γ -> MonTy Γ.

  Arguments Ty_var {_} _.
  Arguments function {_} _ _.

  Notation "A ⟶ B" := (function A B) (at level 70, right associativity) : signature.

  (** Polymorphic types *)
  Inductive PolTy : TyCon -> Kind -> Type :=
  | MonToPol : forall (Γ : TyCon), MonTy Γ -> PolTy Γ ⋆
  | Pi : forall (Γ : TyCon) (k : Kind),
      PolTy (⋆,, Γ) k
      ->
      PolTy Γ (⋆⇒ k).
End Types.

Arguments Ty_var {_} {_} {_} _.
Arguments base {_} {_} {_} _ _.
Arguments function {_} {_} {_} _ _.
Notation "A ⟶ B" := (function A B) (at level 70, right associativity) : signature.

Arguments MonToPol {_} {_} {_} _.
Arguments Pi {_} {_} {_} {_} _.

Coercion MonToPol : MonTy >-> PolTy.
Notation "∏ A" := (Pi A) (at level 60).
