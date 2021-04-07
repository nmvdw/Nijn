Require Import Prelude.All.
Require Import Syntax.Signature.Kinds.
Require Import Syntax.Signature.TypeContexts.
Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.TypeWeakening.

Open Scope signature.

Section Substitution.
  Context {baseTy : Type}
          (ar : baseTy -> Type).

  (** Substitutions between type contexts *)
  Inductive TySub : TyCon -> TyCon -> Type :=
  | Ty_empty : forall (Γ : TyCon), TySub Γ ∙
  | Ty_con : forall {Γ₁ Γ₂ : TyCon} (A : MonTy ar Γ₁), TySub Γ₁ Γ₂ -> TySub Γ₁ (⋆,, Γ₂).

  (** Standard sbustitutions *)
  Definition pr_SubTy
             {Γ₁ Γ₂ : TyCon}
             (s : TySub Γ₁ (⋆,, Γ₂))
    : TySub Γ₁ Γ₂.
  Proof.
    inversion s.
    assumption.
  Defined.

  Definition drop_TySub
             {Γ₁ Γ₂ : TyCon}
             (s : TySub Γ₁ Γ₂)
    : TySub (⋆,, Γ₁) Γ₂.
  Proof.
    induction s as [ Γ | Γ₁ Γ₂ A s ].
    - exact (Ty_empty _).
    - exact (Ty_con (wk_MonTy ar (drop_TyWk (id_TyWk _)) A) IHs).
  Defined.

  Definition keep_TySub
             {Γ₁ Γ₂ : TyCon}
             (s : TySub Γ₁ Γ₂)
    : TySub (⋆,, Γ₁) (⋆,, Γ₂)
    := Ty_con (Ty_var TyVz) (drop_TySub s).

  Definition TyWkToTySub
             {Γ₁ Γ₂ : TyCon}
             (s : TyWk Γ₁ Γ₂)
    : TySub Γ₁ Γ₂.
  Proof.
    induction s as [ | Γ₁ Γ₂ s IHs | Γ₁ Γ₂ s IHs ].
    - apply Ty_empty.
    - exact (drop_TySub IHs).
    - exact (keep_TySub IHs).
  Defined.
      
  Definition id_SubTy
             (Γ : TyCon)
    : TySub Γ Γ.
  Proof.
    induction Γ as [ | Γ IHΓ ].
    - apply Ty_empty.
    - exact (keep_TySub IHΓ).
  Defined.
  
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
      apply keep_TySub.
      exact s.
  Defined.
End Substitution.
