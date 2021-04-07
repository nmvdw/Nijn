Require Import Prelude.All.

Declare Scope signature.
Open Scope signature.

(**
The type of kinds
 *)
Inductive Kind : Type :=
| star : Kind
| arrow : Kind -> Kind.

(**
Notation for the kinds
 *)
Notation "'⋆'" := star : signature.
Notation "'⋆⇒' k" := (arrow k) (at level 70) : signature.

(**
Injectivity of arrow
 *)
Definition arrow_inj
           {k₁ k₂ : Kind}
           (p : ⋆⇒ k₁ = ⋆⇒ k₂)
  : k₁ = k₂.
Proof.
  inversion p.
  reflexivity.
Qed.
  
(**
Kinds have decidable equality
 *)
Definition kind_eq_fam
           (k : Kind)
  : Prop
  := match k with
     | ⋆ => True
     | ⋆⇒ _ => False
     end.

Fixpoint decide_equality_kind
         (k₁ k₂ : Kind)
  : dec (k₁ = k₂)
  := match k₁, k₂ with
     | ⋆ , ⋆ => yes eq_refl
     | ⋆ , ⋆⇒ k₂ => no (fun (p : ⋆ = ⋆⇒ _) => transport kind_eq_fam p I)
     | ⋆⇒ k₁ , ⋆ => no (fun (p : ⋆⇒ _ = ⋆) => transport kind_eq_fam (eq_sym p) I)
     | ⋆⇒ k₁ , ⋆⇒ k₂ =>
       match decide_equality_kind k₁ k₂ with
       | yes p => yes (ap (fun k => ⋆⇒ k) p)
       | no q => no (fun p => q (arrow_inj p))
       end
     end.

Global Instance decEq_kind
  : decEq Kind
  := {| dec_eq := decide_equality_kind |}.
