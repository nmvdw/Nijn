Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.

Declare Scope srp.

(** * Strong reduction pairs *)

(** A strong reduction pair provides two relations on the terms. These relations are respected by the term formers and substitution *)
Section StrongReductionPair.
  Context {B F : Type}
          (ar : F -> ty B).

  Record term_order : Type :=
    make_term_order
      {
        tm_gt : forall (C : con B) (A : ty B),
                  tm ar C A -> tm ar C A -> Prop ;
        tm_ge : forall (C : con B) (A : ty B),
                  tm ar C A -> tm ar C A -> Prop
      }.

  Local Notation "x ≺[ O ] y" := (tm_gt O _ _ x y) (at level 70).
  Local Notation "x ≼[ O ] y" := (tm_ge O _ _ x y) (at level 70).
  
  Definition term_CompatRel
             (C : con B)
             (A : ty B)
             (O : term_order)
    : CompatRel
    := Build_CompatRel (tm ar C A) (tm_gt O C A) (tm_ge O C A).

  Class is_strong_reduction_pair (O : term_order) : Type :=
    {
      gt_isWf : forall (C : con B) (A : ty B),
                  Wf (fun (t₁ t₂ : tm ar C A) => t₁ ≺[ O ] t₂) ;
      compatibility : forall (C : con B) (A : ty B),
                        isCompatRel (term_CompatRel C A O) ;
      sub_gt : forall (C₁ C₂ : con B)
                      (s : sub ar C₁ C₂)
                      (A : ty B)
                      (t₁ t₂ : tm ar C₂ A),
                 t₁ ≺[ O ] t₂
                 -> t₁ [ s ] ≺[ O ] t₂ [ s ] ;
      sub_ge : forall (C₁ C₂ : con B)
                      (s : sub ar C₁ C₂)
                      (A : ty B)
                      (t₁ t₂ : tm ar C₂ A),
                 t₁ ≼[ O ] t₂
                 -> t₁ [ s ] ≼[ O ] t₂ [ s ] ;
      app_gt_l : forall (C : con B)
                        (A₁ A₂ : ty B)
                        (f₁ f₂ : tm ar C (A₁ ⟶ A₂))
                        (t : tm ar C A₁),
                   f₁ ≺[ O ] f₂
                   -> (f₁ · t) ≺[ O ] (f₂ · t) ;
      app_gt_r : forall (C : con B)
                        (A₁ A₂ : ty B)
                        (f : tm ar C (A₁ ⟶ A₂))
                        (t₁ t₂ : tm ar C A₁),
                   t₁ ≺[ O ] t₂
                   -> (f · t₁) ≺[ O ] (f · t₂) ;
      app_ge : forall (C : con B)
                      (A₁ A₂ : ty B)
                      (f₁ f₂ : tm ar C (A₁ ⟶ A₂))
                      (t₁ t₂ : tm ar C A₁),
                 f₁ ≼[ O ] f₂
                 -> t₁ ≼[ O ] t₂
                 -> (f₁ · t₁) ≼[ O ] (f₂ · t₂) ;
      lam_gt : forall (C : con B)
                      (A₁ A₂ : ty B)
                      (f₁ f₂ : tm ar (A₁ ,, C) A₂),
                 f₁ ≺[ O ] f₂
                 -> λ f₁ ≺[ O ] λ f₂ ;
      lam_ge : forall (C : con B)
                      (A₁ A₂ : ty B)
                      (f₁ f₂ : tm ar (A₁ ,, C) A₂),
                 f₁ ≼[ O ] f₂
                 -> λ f₁ ≼[ O ] λ f₂ ;
      beta_ge : forall (C : con B)
                       (A₁ A₂ : ty B)
                       (f : tm ar (A₁ ,, C) A₂)
                       (t : tm ar C A₁),
                  (λ f) · t ≼[ O ] f [ beta_sub t ]
    }.
  
  Record strong_reduction_pair : Type :=
    make_srp
      {
        orders :> term_order ;
        is_srp : is_strong_reduction_pair orders
      }.

  Global Instance strong_reduction_pair_is_srp
                  (srp : strong_reduction_pair)
    : is_strong_reduction_pair srp
    := is_srp srp.
End StrongReductionPair.

Notation "x ≺[ O ] y" := (tm_gt _ O _ _ x y) (at level 70) : srp.
Notation "x ≼[ O ] y" := (tm_ge _ O _ _ x y) (at level 70) : srp.
