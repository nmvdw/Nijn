Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.
Require Import Syntax.Signature.TermWeakenings.
Require Import Syntax.Signature.TermSubstitutions.

(** * Rewriting systems *)

(** To formulate the beta rule, we need a particular substitution *)
Definition beta_sub
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : sub ar C (A ,, C)
  := ExtendSub (idSub C ar) t.

(** ** Beta reduction in an AFS *)
Inductive betaRed
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          {C : con B}
  : forall {A : ty B}, tm ar C A -> tm ar C A -> Prop
  :=
| BetaTrans : forall {A : ty B}
                     {t1 t2 t3 : tm ar C A},
    betaRed t1 t2 -> betaRed t2 t3 -> betaRed t1 t3
| BetaRew_App_l : forall {A1 A2 : ty B}
                         {f1 f2 : tm ar C (A1 ⟶ A2)}
                         (x : tm ar C A1),
    betaRed f1 f2 -> betaRed (f1 · x) (f2 · x)
| BetaRew_App_r : forall {A1 A2 : ty B}
                         (f : tm ar C (A1 ⟶ A2))
                         {x1 x2 : tm ar C A1},
    betaRed x1 x2 -> betaRed (f · x1) (f · x2)
| BetaRew_Lam : forall {A1 A2 : ty B}
                       {f1 f2 : tm ar (A1 ,, C) A2},
    betaRed f1 f2 -> betaRed (λ f1) (λ f2)
| BetaBeta : forall {A1 A2 : ty B}
                    (f : tm ar (A1 ,, C) A2)
                    (x : tm ar C A1),
    betaRed ((λ f) · x) (subTm f (beta_sub x)).

Arguments BetaTrans {_ _ _ _} {_ _ _ _} _ _.
Arguments BetaRew_App_l {_ _ _ _} {_ _ _ _} _ _.
Arguments BetaRew_App_r {_ _ _ _} {_ _} _ {_ _} _.
Arguments BetaRew_Lam {_ _ _ _} {_ _ _ _} _.
Arguments BetaBeta {_ _ _ _} {_ _} _ _.

(** ** The rewriting relation in an AFS *)
Inductive rew
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          {R : Type}
          {Rcon : R -> con B}
          {Rtar : R -> B}
          (lhs rhs : forall (r : R), tm ar (Rcon r) (Base (Rtar r)))
          {C : con B}
  : forall {A : ty B}, tm ar C A -> tm ar C A -> Prop
  :=
| Trans : forall {A : ty B}
                 {t1 t2 t3 : tm ar C A},
    rew lhs rhs t1 t2 -> rew lhs rhs t2 t3 -> rew lhs rhs t1 t3
| Rew_App_l : forall {A1 A2 : ty B}
                     {f1 f2 : tm ar C (A1 ⟶ A2)}
                     (x : tm ar C A1),
    rew lhs rhs f1 f2 -> rew lhs rhs (f1 · x) (f2 · x)
| Rew_App_r : forall {A1 A2 : ty B}
                     (f : tm ar C (A1 ⟶ A2))
                     {x1 x2 : tm ar C A1},
    rew lhs rhs x1 x2 -> rew lhs rhs (f · x1) (f · x2)
| Rew_Lam : forall {A1 A2 : ty B}
                   {f1 f2 : tm ar (A1 ,, C) A2},
    rew lhs rhs f1 f2 -> rew lhs rhs (λ f1) (λ f2)
| Beta : forall {A1 A2 : ty B}
                (f : tm ar (A1 ,, C) A2)
                (x : tm ar C A1),
    rew lhs rhs ((λ f) · x) (subTm f (beta_sub x))
| BaseRew : forall (r : R)
                   (s : sub ar C (Rcon r)),
    rew lhs rhs (subTm (lhs r) s) (subTm (rhs r) s).

Arguments Trans {_ _ _ _ _ _ _ _ _} {_ _ _ _} _ _.
Arguments Rew_App_l {_ _ _ _ _ _ _ _ _} {_ _ _ _} _ _.
Arguments Rew_App_r {_ _ _ _ _ _ _ _ _} {_ _} _ {_ _} _.
Arguments Rew_Lam {_ _ _ _ _ _ _ _ _} {_ _ _ _} _.
Arguments Beta {_ _ _ _ _ _ _ _ _} {_ _} _ _.
Arguments BaseRew {_ _ _ _ _ _ _ _ _} _ _.
