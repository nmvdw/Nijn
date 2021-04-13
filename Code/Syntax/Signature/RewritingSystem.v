Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.
Require Import Syntax.Signature.TermWeakenings.
Require Import Syntax.Signature.TermSubstitutions.

Inductive Rew
          {B : Type}
          {F : Type}
          {ar : F -> Ty B}
          {R : Type}
          {Rcon : R -> Con B}
          {Rtar : R -> Ty B}
  : forall (lhs rhs : forall (r : R), Tm ar (Rcon r) (Rtar r))
           {C : Con B}
           {A : Ty B},
    Tm ar C A -> Tm ar C A -> Type
  :=
| Trans : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Rtar r)}
                 {C : Con B}
                 {A : Ty B}
                 {t1 t2 t3 : Tm ar C A},
    Rew lhs rhs t1 t2 -> Rew lhs rhs t2 t3 -> Rew lhs rhs t1 t3
| Rew_App_l : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Rtar r)}
                     {C : Con B}
                     {A B : Ty B}
                     {f1 f2 : Tm ar C (A ⟶ B)}
                     (x : Tm ar C A),
    Rew lhs rhs f1 f2 -> Rew lhs rhs (f1 · x) (f2 · x)
| Rew_App_r : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Rtar r)}
                     {C : Con B}
                     {A B : Ty B}
                     (f : Tm ar C (A ⟶ B))
                     {x1 x2 : Tm ar C A},
    Rew lhs rhs x1 x2 -> Rew lhs rhs (f · x1) (f · x2)
| Rew_Lam : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Rtar r)}
                   {C : Con B}
                   {A B : Ty B}
                   {f1 f2 : Tm ar (A ,, C) B},
    Rew lhs rhs f1 f2 -> Rew lhs rhs (λ f1) (λ f2)
| BaseRew : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Rtar r)}
                   {C : Con B}
                   (r : R)
                   (s : Sub ar C (Rcon r)),
    Rew lhs rhs (subTm (lhs r) s) (subTm (rhs r) s).
