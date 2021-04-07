Require Import Prelude.All.
Require Import Syntax.Signature.Kinds.
Require Import Syntax.Signature.TypeContexts.
Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.TypeWeakening.
Require Import Syntax.Signature.TypeSubstitution.
Require Import Syntax.Signature.TermContexts.

Open Scope signature.

Section Terms.
  Context {baseTy : Type}
          (ar : baseTy -> Type).

  (** Terms of a monomorphic type *)
  Inductive MonTm : forall (Γ : TyCon), TmCon ar Γ -> MonTy ar Γ -> Type :=
  | Tm_var : forall {Γ : TyCon} {Δ : TmCon ar Γ} {A : MonTy ar Γ},
      TmVar ar Δ A -> MonTm Γ Δ A
  | lambda : forall {Γ : TyCon}
                    {Δ : TmCon ar Γ}
                    {A B : MonTy ar Γ},
      MonTm Γ (A ,, Δ) B
      -> MonTm Γ Δ (A ⟶ B)
  | app : forall {Γ : TyCon}
                 {Δ : TmCon ar Γ}
                 {A B : MonTy ar Γ},
      MonTm Γ Δ (A ⟶ B)
      -> MonTm Γ Δ A
      -> MonTm Γ Δ B.

  Inductive PolTm : forall {Γ : TyCon} {k : Kind}, TmCon ar Γ -> PolTy ar Γ k -> Type :=
  | MonToPolTm : forall {Γ : TyCon} {Δ : TmCon ar Γ} {A : MonTy ar Γ},
      MonTm Γ Δ A -> PolTm Δ A
  | App : forall {Γ : TyCon}
                 {k : Kind}
                 {Δ : TmCon ar Γ}
                 {A : PolTy ar (⋆,, Γ) k}
                 (B : MonTy ar Γ),
      PolTm Δ (∏ A)
      -> PolTm Δ (sub_PolTy ar (Ty_con _ B (id_SubTy _ _)) A)
  | Lambda : forall {Γ : TyCon}
                    {k : Kind}
                    {Δ : TmCon ar Γ}
                    {A : PolTy ar (⋆,, Γ) k},
      PolTm (wk_TmCon (drop_TyWk (id_TyWk _)) Δ) A
      -> PolTm Δ (∏ A).

  Coercion MonToPolTm : MonTm >-> PolTm.

  Notation "'Λ' x" := (Lambda x) (at level 10) : signature.
  Notation "'λ' x" := (lambda x) (at level 10) : signature.
  Notation "f · x" := (app f x) (at level 20, left associativity) : signature.

  (** Examples of terms *)
  Example poly_id_Ty
    : PolTy ar ∙ (⋆⇒ ⋆)
    := let a := Ty_var TyVz in
       ∏ (a ⟶ a).

  Example poly_id_Tm
    : PolTm ∙∙ poly_id_Ty
    := let x := Tm_var TmVz in
       Λ λ x.

  Example poly_fst_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ ⋆))
    := let a := Ty_var TyVz in
       let b := Ty_var (TyVs TyVz) in
       ∏ ∏ (a ⟶ b ⟶ a).

  Example poly_fst_Tm
    : PolTm ∙∙ poly_fst_Ty
    := let x := Tm_var (TmVs TmVz) in
       Λ Λ λ λ x.

  Example poly_snd_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ ⋆))
    := let a := Ty_var TyVz in
       let b := Ty_var (TyVs TyVz) in
       ∏ ∏ (a ⟶ b ⟶ b).

  Example poly_snd_Tm
    : PolTm ∙∙ poly_snd_Ty
    := let y := Tm_var TmVz in
       Λ Λ λ λ y.

  Example poly_comp_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ (⋆⇒ ⋆)))
    := let a := Ty_var TyVz in
       let b := Ty_var (TyVs TyVz) in
       let c := Ty_var (TyVs (TyVs TyVz)) in
       ∏ ∏ ∏ ((a ⟶ b) ⟶ (b ⟶ c) ⟶ a ⟶ c).

  Example poly_comp_Tm
    : PolTm ∙∙ poly_comp_Ty
    := let f := Tm_var (TmVs (TmVs TmVz)) in
       let g := Tm_var (TmVs TmVz) in
       let x := Tm_var TmVz in
       Λ Λ Λ λ λ λ (g · (f · x)).

  Example poly_app_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ ⋆))
    := let a := Ty_var TyVz in
       let b := Ty_var (TyVs TyVz) in
       ∏ ∏ ((a ⟶ b) ⟶ a ⟶ b).

  Example poly_app_Tm
    : PolTm ∙∙ poly_app_Ty
    := let f := Tm_var (TmVs TmVz) in
       let x := Tm_var TmVz in
       Λ Λ λ λ (f · x).

  Example poly_app2_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ (⋆⇒ ⋆)))
    := let a := Ty_var TyVz in
       let b := Ty_var (TyVs TyVz) in
       let c := Ty_var (TyVs (TyVs TyVz)) in
       ∏ ∏ ∏ ((a ⟶ b ⟶ c) ⟶ a ⟶ b ⟶ c).

  Example poly_app2_Tm
    : PolTm ∙∙ poly_app2_Ty
    := let y := Tm_var TmVz in
       let x := Tm_var (TmVs TmVz) in
       let f := Tm_var (TmVs (TmVs TmVz)) in
       Λ Λ Λ λ λ λ (f · x · y).

  Example poly_S_Ty
    : PolTy ar ∙ (⋆⇒ (⋆⇒ (⋆⇒ ⋆)))
    := let a := Ty_var TyVz in
       let b := Ty_var (TyVs TyVz) in
       let c := Ty_var (TyVs (TyVs TyVz)) in
       ∏ ∏ ∏ ((a ⟶ b ⟶ c) ⟶ (a ⟶ b) ⟶ a ⟶ c).

  Example poly_S_Tm
    : PolTm ∙∙ poly_S_Ty
    := let x := Tm_var (TmVs (TmVs TmVz)) in
       let y := Tm_var (TmVs TmVz) in
       let z := Tm_var TmVz in
       Λ Λ Λ λ λ λ (x · z · (y · z)).
  
  Example poly_false_Ty
    : PolTy ar ∙ (⋆⇒ ⋆)
    := let a := Ty_var TyVz in
       ∏ a.

  Example id_on_Ty
          (a : MonTy ar ∙)
    : PolTm ∙∙ (a ⟶ a)
    := App a poly_id_Tm.
End Terms.




