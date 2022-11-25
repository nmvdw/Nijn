Require Import Nijn.Prelude.
Require Export Nijn.Syntax.Signature.Types.
Require Export Nijn.Syntax.Signature.Contexts.
Require Export Nijn.Syntax.Signature.Terms.
Require Export Nijn.Syntax.Signature.TermWeakenings.
Require Export Nijn.Syntax.Signature.TermSubstitutions.
Require Export Nijn.Syntax.Signature.RewritingSystem.

(** * The notion of Algebraic Functional System *)
Record rewriteRule {B : Type} {F : Type} (ar : F -> ty B) :=
  make_rewrite
    {
      vars_of : con B ;
      tar_of : ty B ;
      lhs_of : tm ar vars_of tar_of ;
      rhs_of : tm ar vars_of tar_of
    }.

Arguments make_rewrite {_ _ _} _ _ _ _.
Arguments vars_of {_ _ _} _.
Arguments tar_of {_ _ _} _.
Arguments lhs_of {_ _ _} _.
Arguments rhs_of {_ _ _} _.

Program Definition dec_eq_rewriteRule
                   {B : Type}
                   `{decEq B}
                   {F : Type}
                   `{decEq F}
                   {ar : F -> ty B}
                   (r₁ r₂ : rewriteRule ar)
  : dec (r₁ = r₂)
  := match dec_eq (vars_of r₁) (vars_of r₂) with
     | Yes p₁ =>
       match dec_eq (tar_of r₁) (tar_of r₂) with
       | Yes p₂ =>
         match dec_eq (tm_to_ut_tm (lhs_of r₁)) (tm_to_ut_tm (lhs_of r₂)) with
         | Yes p₃ =>
           match dec_eq (tm_to_ut_tm (rhs_of r₁)) (tm_to_ut_tm (rhs_of r₂)) with
           | Yes p₄ => Yes _
           | No _ => No _
           end
         | No _ => No _
         end
       | No _ => No _
       end
     | No _ => No _
     end.
Next Obligation.
  destruct r₁ as [ v₁ t₁ l₁ r₁ ].
  destruct r₂ as [ v₂ t₂ l₂ r₂ ].
  cbn in *.
  subst.
  f_equal ; [ apply (eq_ut_tm p₃ (eq_refl _)) |  apply (eq_ut_tm p₄ (eq_refl _)) ].
Qed.

Global Instance decEq_rewriteRule
                {B : Type}
                `{decEq B}
                {F : Type}
                `{decEq F}
                (ar : F -> ty B)
  : decEq (rewriteRule ar)
  := {| dec_eq := dec_eq_rewriteRule |}.

Record afs (B : Type) (F : Type) :=
  make_afs
    {
      arity : F -> ty B ;
      list_of_rewriteRules : list (rewriteRule arity)
    }.

Arguments make_afs {_ _} _ _.
Arguments arity {_ _} _ _.
Arguments list_of_rewriteRules {_ _} _.

Record fin_afs (B : Type) (F : Type) :=
  make_fin_afs
    {
      carrier :> afs B F ;
      baseTyFin : isFinite B ;
      baseTmFin : isFinite F
    }.

Arguments make_fin_afs {_ _} _ _ _.
Arguments carrier {_ _} _.
Arguments baseTyFin {_ _} _.
Arguments baseTmFin {_ _} _.

Definition rewriteRules
           {B F : Type}
           (X : afs B F)
  : Type
  := members (list_of_rewriteRules X).

Definition vars
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : con B
  := vars_of (member_el r).

Definition tars
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : ty B
  := tar_of (member_el r).

Definition lhs
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : tm (arity X) (vars r) (tars r)
  := lhs_of (member_el r).

Definition rhs
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : tm (arity X) (vars r) (tars r)
  := rhs_of (member_el r).

(** Accessor functions for AFSs *)
Module AFSNotation.
  Definition tm
             {B : Type}
             {F : Type}
             (X : afs B F)
             (C : con B)
             (A : ty B)
  : Type
    := Terms.tm (arity X) C A.

  Definition betaRed
             {B : Type}
             {F : Type}
             (X : afs B F)
             {C : con B}
             {A : ty B}
             (t1 t2 : tm X C A)
    : Type
    := RewritingSystem.betaRed t1 t2.

  Definition rew
             {B : Type}
             {F : Type}
             (X : afs B F)
             {C : con B}
             {A : ty B}
             (t1 t2 : tm X C A)
    := RewritingSystem.rew lhs rhs t1 t2.

  Notation "t1 ∼> t2" := (rew _ t1 t2) (at level 70). (* \sim is used *)
End AFSNotation.

Import AFSNotation.

Definition rew_rewrite_rule
           {B : Type}
           {F : Type}
           (X : afs B F)
           (r : rewriteRules X)
           {C : con B}
           (s : sub (arity X) C (vars r))
  : lhs r [ s ] ∼> rhs r [ s ].
Proof.
  apply rew_baseStep.
Defined.
