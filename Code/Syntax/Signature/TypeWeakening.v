Require Import Prelude.All.
Require Import Syntax.Signature.Kinds.
Require Import Syntax.Signature.TypeContexts.
Require Import Syntax.Signature.Types.

Open Scope signature.

Section Weakening.
  Context {baseTy : Type}
          (ar : baseTy -> Type).

  (** Substitutions between type contexts *)
  Inductive TyWk : TyCon -> TyCon -> Type :=
  | empty_TyWk : TyWk ∙ ∙
  | drop_TyWk : forall {Γ₁ Γ₂ : TyCon}, TyWk Γ₁ Γ₂ -> TyWk (⋆,, Γ₁) Γ₂
  | keep_TyWk : forall {Γ₁ Γ₂ : TyCon}, TyWk Γ₁ Γ₂ -> TyWk (⋆,, Γ₁) (⋆,, Γ₂).

  (** Identity weakening *)
  Fixpoint id_TyWk
           (Γ : TyCon)
    : TyWk Γ Γ
    := match Γ with
       | ∙ => empty_TyWk
       | ⋆,, Γ => keep_TyWk (id_TyWk Γ)
       end.

  (** Composition of weakenings *)
  Definition comp_TyWk
             {Γ₁ Γ₂ Γ₃ : TyCon}
             (s₁ : TyWk Γ₁ Γ₂)
             (s₂ : TyWk Γ₂ Γ₃)
    : TyWk Γ₁ Γ₃.
  Proof.
    induction s₁ as [ | Γ₁ Γ₂ s₁ IHs₁ | Γ₁ Γ₂ s₁ IHs₁ ].
    - exact s₂.
    - apply drop_TyWk.
      apply IHs₁.
      exact s₂.
    - inversion s₂.
      + apply drop_TyWk.
        apply IHs₁.
        assumption.
      + admit.
  Admitted.
  
  (** Remove all variables *)
  Fixpoint toEmpty_TyWk
           (Γ : TyCon)
    : TyWk Γ ∙
    := match Γ with
       | ∙ => empty_TyWk
       | ⋆,, Γ => drop_TyWk (toEmpty_TyWk Γ)
       end.

  (** Weakening of variables *)
  Definition wk_TyVar
             {Γ₁ Γ₂ : TyCon}
             (s : TyWk Γ₁ Γ₂)
             (v : TyVar Γ₂)
    : TyVar Γ₁.
  Proof.
    induction s.
    - exact v.
    - apply TyVs.
      apply IHs.
      exact v.
    - inversion v.
      + apply TyVz.
      + apply TyVs.
        apply IHs.
        assumption.
  Defined.

  (** Weakening of monomorphic types *)
  Definition wk_MonTy
             {Γ₁ Γ₂ : TyCon}
             (s : TyWk Γ₁ Γ₂)
             (A : MonTy ar Γ₂)
    : MonTy ar Γ₁.
  Proof.
    induction A as [ Γ₂ v | Γ₂ b A IHA | Γ₂ A₁ IHA₁ A₂ IHA₂ ].
    - exact (Ty_var (wk_TyVar s v)).
    - exact (base b (fun z => IHA z s)).
    - exact (IHA₁ s ⟶ IHA₂ s).
  Defined.

  (** Weakening of monomorphic types *)
  Definition wk_PolTy
             {Γ₁ Γ₂ : TyCon}
             (s : TyWk Γ₁ Γ₂)
             {k : Kind}
             (A : PolTy ar Γ₂ k)
    : PolTy ar Γ₁ k.
  Proof.
    revert s.
    revert Γ₁.
    induction A as [ Γ A | Γ k A ].
    - intros Γ₁ s.
      exact (MonToPol (wk_MonTy s A)).
    - intros Γ₁ s.
      refine (∏ _).
      apply IHA.
      apply keep_TyWk.
      exact s.
  Defined.
End Weakening.
