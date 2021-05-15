Require Import Prelude.Basics.
Require Export Syntax.Signature.Types.
Require Export Syntax.Signature.Contexts.
Require Export Syntax.Signature.Terms.
Require Export Syntax.Signature.TermWeakenings.
Require Export Syntax.Signature.TermSubstitutions.
Require Export Syntax.Signature.RewritingSystem.

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
End AFSNotation.
