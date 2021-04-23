Require Export Syntax.Signature.Types.
Require Export Syntax.Signature.Contexts.
Require Export Syntax.Signature.Terms.
Require Export Syntax.Signature.TermWeakenings.
Require Export Syntax.Signature.TermSubstitutions.
Require Export Syntax.Signature.RewritingSystem.

(** * The notion of Algebraic Functional System *)
Record afs (B : Type) (F : Type) (R : Type) :=
  {
    Arity : F -> ty B ;
    Vars : R -> con B ;
    Tars : R -> B ;
    Lhs : forall (r : R), tm Arity (Vars r) (Base (Tars r)) ;
    Rhs : forall (r : R), tm Arity (Vars r) (Base (Tars r))
  }.

Arguments Arity {_ _ _}.
Arguments Vars {_ _ _}.
Arguments Tars {_ _ _}.
Arguments Lhs {_ _ _}.
Arguments Rhs {_ _ _}.

(** Accessor functions for AFSs *)
Module AFSNotation.
  Definition tm
             {B : Type}
             {F : Type}
             {R : Type}
             (X : afs B F R)
             (C : con B)
             (A : ty B)
  : Type
    := Terms.tm (Arity X) C A.

  Definition betaRed
             {B : Type}
             {F : Type}
             {R : Type}
             (X : afs B F R)
             {C : con B}
             {A : ty B}
             (t1 t2 : tm X C A)
    : Type
    := RewritingSystem.betaRed t1 t2.

  Definition rew
             {B : Type}
             {F : Type}
             {R : Type}
             (X : afs B F R)
             {C : con B}
             {A : ty B}
             (t1 t2 : tm X C A)
    : Type
    := RewritingSystem.rew (Lhs X) (Rhs X) t1 t2.
End AFSNotation.
