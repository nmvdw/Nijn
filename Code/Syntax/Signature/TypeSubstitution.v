Require Import Prelude.All.
Require Import Syntax.Signature.Kinds.
Require Import Syntax.Signature.TypeContexts.
Require Import Syntax.Signature.Types.

Open Scope signature.

Section Substitution.
  Context {baseTy : Type}
          (ar : baseTy -> Type).

  (** Substitutions between type contexts *)
  Inductive TySub : TyCon -> TyCon -> Type :=
  | Ty_empty : forall (Γ : TyCon), TySub Γ ∙
  | Ty_con : forall {Γ₁ Γ₂ : TyCon} (A : MonTy ar Γ₁), TySub Γ₁ Γ₂ -> TySub Γ₁ (⋆,, Γ₂).

  (** Substitution of variables *)
  Definition sub_TyVar
             {Γ₁ Γ₂ : TyCon}
             (s : TySub Γ₁ Γ₂)
             (v : TyVar Γ₂)
    : MonTy ar Γ₁.
  Proof.
    induction v.
    - inversion s.
      exact A.
    - inversion s.
      apply IHv.
      exact X.
  Defined.

  (** Substitution of variables *)
  Definition sub_MonTy
             {Γ₁ Γ₂ : TyCon}
             (s : TySub Γ₁ Γ₂)
             (A : MonTy ar Γ₂)
    : MonTy ar Γ₁.
  Proof.
    induction A as [ Γ₂ v | Γ₂ b A IHA | Γ₂ A₁ IHA₁ A₂ IHA₂ ].
    - exact (sub_TyVar s v).
    - exact (base b (fun z => IHA z s)).
    - exact (IHA₁ s ⟶ IHA₂ s).
  Defined.

  Definition sub_PolTy
             {Γ₁ Γ₂ : TyCon}
             (s : TySub Γ₁ Γ₂)
             {k : Kind}
             (A : PolTy ar Γ₂ k)
    : PolTy ar Γ₁ k.
  Proof.
    revert s.
    revert Γ₁.
    induction A as [ Γ A | Γ k A ].
    - intros Γ₁ s.
      exact (MonToPol (sub_MonTy s A)).
    - intros Γ₁ s.
      refine (∏ _).
      apply IHA.
  Admitted.

  Definition id_SubTy
             (Γ : TyCon)
    : TySub Γ Γ.
  Admitted.
End Substitution.
