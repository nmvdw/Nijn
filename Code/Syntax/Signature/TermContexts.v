Require Import Prelude.All.
Require Import Syntax.Signature.Kinds.
Require Import Syntax.Signature.TypeContexts.
Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.TypeWeakening.
Require Import Syntax.Signature.TypeSubstitution.

Open Scope signature.

Section Contexts.
  Context {baseTy : Type}
          (ar : baseTy -> Type).

  (** Contexts *)
  Inductive TmCon : TyCon -> Type :=
  | empty : forall (Γ : TyCon), TmCon Γ
  | extend : forall (Γ : TyCon), MonTy ar Γ -> TmCon Γ -> TmCon Γ.

  Definition wk_TmCon
             {Γ₁ Γ₂ : TyCon}
             (s : TyWk Γ₁ Γ₂)
             (Δ : TmCon Γ₂)
    : TmCon Γ₁.
  Proof.
    induction Δ.
    - apply empty.
    - exact (extend _ (wk_MonTy _ s m) (IHΔ s)).
  Defined.

  Definition sub_TmCon
             {Γ₁ Γ₂ : TyCon}
             (s : TySub ar Γ₁ Γ₂)
             (Δ : TmCon Γ₂)
    : TmCon Γ₁.
  Proof.
    induction Δ.
    - apply empty.
    - exact (extend _ (sub_MonTy _ s m) (IHΔ s)).
  Defined.

  (** Variables in a context *)
  Inductive TmVar : forall {Γ : TyCon}, TmCon Γ -> MonTy ar Γ -> Type :=
  | TmVz : forall {Γ : TyCon} {Δ : TmCon Γ} {A : MonTy ar Γ}, TmVar (extend _ A Δ) A
  | TmVs : forall {Γ : TyCon} {Δ : TmCon Γ} {A B : MonTy ar Γ},
      TmVar Δ A
      -> TmVar (extend _ B Δ) A.
End Contexts.

Arguments empty {_} {_} {_}.
Notation "∙∙" := empty : signature.

Arguments extend {_} {_} {_} _ _.
Notation "A ,, Γ" :=  (extend A Γ) (at level 70, right associativity) : signature.

Arguments wk_TmCon {_} {_} {_} {_} _ _.
Arguments sub_TmCon {_} {_} {_} {_} _ _.

Arguments TmVz {_} {_} {_} {_} {_}.
Arguments TmVs {_} {_} {_} {_} {_} {_} _.
