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
      Vars : con B ;
      Tar : ty B ;
      Lhs : tm ar Vars Tar ;
      Rhs : tm ar Vars Tar
    }.

Arguments make_rewrite {_ _ _} _ _ _ _.
Arguments Vars {_ _ _} _.
Arguments Tar {_ _ _} _.
Arguments Lhs {_ _ _} _.
Arguments Rhs {_ _ _} _.

Record afs (B : Type) (F : Type) :=
  make_afs
    {
      Arity : F -> ty B ;
      RewriteRules : list (rewriteRule Arity)
    }.

Arguments make_afs {_ _} _ _.
Arguments Arity {_ _} _ _.
Arguments RewriteRules {_ _} _.

Definition rewriteRules
           {B F : Type}
           (X : afs B F)
  : Type
  := members (RewriteRules X).

Definition vars
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : con B
  := Vars (member_el r).

Definition tars
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : ty B
  := Tar (member_el r).

Definition lhs
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : tm (Arity X) (vars r) (tars r)
  := Lhs (member_el r).

Definition rhs
           {B F : Type}
           {X : afs B F}
           (r : rewriteRules X)
  : tm (Arity X) (vars r) (tars r)
  := Rhs (member_el r).

(** Accessor functions for AFSs *)
Module AFSNotation.
  Definition tm
             {B : Type}
             {F : Type}
             (X : afs B F)
             (C : con B)
             (A : ty B)
  : Type
    := Terms.tm (Arity X) C A.

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
