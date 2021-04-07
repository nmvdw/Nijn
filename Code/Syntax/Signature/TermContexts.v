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

  (** Terms of a monomorphic type *)
  Inductive MonTm : forall (Γ : TyCon), TmCon Γ -> MonTy ar Γ -> Type :=
  | var' : forall {Γ : TyCon} {Δ : TmCon Γ} {A : MonTy ar Γ},
      TmVar Δ A -> MonTm Γ Δ A
  | lambda : forall {Γ : TyCon}
                    {Δ : TmCon Γ}
                    {A B : MonTy ar Γ},
      MonTm Γ (extend _ A Δ) B
      -> MonTm Γ Δ (A ⟶ B)
  | app : forall {Γ : TyCon}
                 {Δ : TmCon Γ}
                 {A B : MonTy ar Γ},
      MonTm Γ Δ (A ⟶ B)
      -> MonTm Γ Δ A
      -> MonTm Γ Δ B.

  Inductive PolTm : forall {Γ : TyCon} {k : Kind}, TmCon Γ -> PolTy ar Γ k -> Type :=
  | MonToPolTm : forall {Γ : TyCon} {Δ : TmCon Γ} {A : MonTy ar Γ},
      MonTm Γ Δ A -> PolTm Δ A
  | App : forall {Γ : TyCon}
                 {k : Kind}
                 {Δ : TmCon Γ}
                 {A : PolTy ar (⋆,, Γ) k}
                 (B : MonTy ar Γ),
      PolTm Δ (∏ A)
      -> PolTm Δ (sub_PolTy ar (Ty_con _ B (id_SubTy _ _)) A)
  | Lambda : forall {Γ : TyCon}
                    {k : Kind}
                    {Δ : TmCon Γ}
                    {A : PolTy ar (⋆,, Γ) k},
      PolTm (wk_TmCon (drop_TyWk (id_TyWk _)) Δ) A
      -> PolTm Δ (∏ A).

  Coercion MonToPolTm : MonTm >-> PolTm.

  Notation "'Λ' x" := (Lambda x) (at level 10) : signature.
  Notation "'λ' x" := (lambda x) (at level 10) : signature.
  Notation "f · x" := (app f x) (at level 20, left associativity) : signature.

  Example poly_id_Ty
    : PolTy ar ∙ (⋆⇒ ⋆)
    := ∏ (var (TyVz _) ⟶ var (TyVz _)).

  Example poly_id_Tm
    : PolTm (empty _) poly_id_Ty
    := Λ λ (var' TmVz).

  Example poly_fst_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ ⋆))
    := ∏ ∏ (var (TyVz _) ⟶ var (TyVs _ (TyVz _)) ⟶ var (TyVz _)).

  Example poly_fst_Tm
    : PolTm (empty _) poly_fst_Ty
    := Λ Λ λ λ (var' (TmVs TmVz)).

  Example poly_snd_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ ⋆))
    := ∏ ∏ (var (TyVz _) ⟶ var (TyVs _ (TyVz _)) ⟶ var (TyVs _ (TyVz _))).

  Example poly_snd_Tm
    : PolTm (empty _) poly_snd_Ty
    := Λ Λ λ λ (var' TmVz).

  Example poly_comp_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ (⋆⇒ ⋆)))
    := let a := var (TyVz _) in
       let b := var (TyVs _ (TyVz _)) in
       let c := var (TyVs _ (TyVs _ (TyVz _))) in
       ∏ ∏ ∏ ((a ⟶ b) ⟶ (b ⟶ c) ⟶ a ⟶ c).

  Example poly_comp_Tm
    : PolTm (empty _) poly_comp_Ty
    := let f := var' (TmVs (TmVs TmVz)) in
       let g := var' (TmVs TmVz) in
       let x := var' TmVz in
       Λ Λ Λ λ λ λ (g · (f · x)).

  Example poly_app_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ ⋆))
    := let a := var (TyVz _) in
       let b := var (TyVs _ (TyVz _)) in
       ∏ ∏ ((a ⟶ b) ⟶ a ⟶ b).

  Example poly_app_Tm
    : PolTm (empty _) poly_app_Ty
    := let f := var' (TmVs TmVz) in
       let x := var' TmVz in
       Λ Λ λ λ (f · x).

  Example poly_app2_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ (⋆⇒ ⋆)))
    := let a := var (TyVz _) in
       let b := var (TyVs _ (TyVz _)) in
       let c := var (TyVs _ (TyVs _ (TyVz _))) in
       ∏ ∏ ∏ ((a ⟶ b ⟶ c) ⟶ a ⟶ b ⟶ c).

  Example poly_app2_Tm
    : PolTm (empty _) poly_app2_Ty
    := let y := var' TmVz in
       let x := var' (TmVs TmVz) in
       let f := var' (TmVs (TmVs TmVz)) in
       Λ Λ Λ λ λ λ (f · x · y).

  Example poly_S_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ (⋆⇒ ⋆)))
    := let a := var (TyVz _) in
       let b := var (TyVs _ (TyVz _)) in
       let c := var (TyVs _ (TyVs _ (TyVz _))) in
       ∏ ∏ ∏ ((a ⟶ b ⟶ c) ⟶ (a ⟶ b) ⟶ a ⟶ c).

  Example poly_S_Tm
    : PolTm (empty _) poly_S_Ty
    := let x := var' (TmVs (TmVs TmVz)) in
       let y := var' (TmVs TmVz) in
       let z := var' TmVz in
       Λ Λ Λ λ λ λ (x · z · (y · z)).
  
  Example poly_false_Ty
    : PolTy ar ∙ (⋆⇒ ⋆)
    := ∏ (var (TyVz _)).

  Example id_on_some_Ty
          (a : MonTy ar ∙)
    : PolTm (empty _) (a ⟶ a).
  Proof.
    pose (App a poly_id_Tm).
    cbn in p.
    Locate sub_PolTy.
End Contexts.




