Require Export Syntax.Signature.Types.
Require Export Syntax.Signature.Contexts.
Require Export Syntax.Signature.Terms.
Require Export Syntax.Signature.TermWeakenings.
Require Export Syntax.Signature.TermSubstitutions.
Require Export Syntax.Signature.RewritingSystem.

Record AFS (B : Type) (F : Type) (R : Type) :=
  {
    Arity : F -> Ty B ;
    Vars : R -> Con B ;
    Tars : R -> B ;
    Lhs : forall (r : R), Tm Arity (Vars r) (Base (Tars r)) ;
    Rhs : forall (r : R), Tm Arity (Vars r) (Base (Tars r))
  }.

Arguments Arity {_ _ _}.
Arguments Vars {_ _ _}.
Arguments Tars {_ _ _}.
Arguments Lhs {_ _ _}.
Arguments Rhs {_ _ _}.

Module AFSNotation.
  Definition Tm
             {B : Type}
             {F : Type}
             {R : Type}
             (X : AFS B F R)
             (C : Con B)
             (A : Ty B)
  : Type
    := Terms.Tm (Arity X) C A.

  Definition BetaRed
             {B : Type}
             {F : Type}
             {R : Type}
             (X : AFS B F R)
             {C : Con B}
             {A : Ty B}
             (t1 t2 : Tm X C A)
    : Prop
    := RewritingSystem.BetaRed t1 t2.

  Definition Rew
             {B : Type}
             {F : Type}
             {R : Type}
             (X : AFS B F R)
             {C : Con B}
             {A : Ty B}
             (t1 t2 : Tm X C A)
    : Prop
    := RewritingSystem.Rew (Lhs X) (Rhs X) t1 t2.
End AFSNotation.
