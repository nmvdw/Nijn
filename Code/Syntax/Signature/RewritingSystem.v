Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.
Require Import Syntax.Signature.TermWeakenings.
Require Import Syntax.Signature.TermSubstitutions.

(*
Inductive Rew
          {B : Type}
          {F : Type}
          {ar : F -> Ty B}
          {R : Type}
          {Rcon : R -> Con B}
          {Rtar : R -> B}
  : forall (lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r)))
           {C : Con B}
           {A : Ty B},
    Tm ar C A -> Tm ar C A -> Type
  :=
| Trans : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r))}
                 {C : Con B}
                 {A : Ty B}
                 {t1 t2 t3 : Tm ar C A},
    Rew lhs rhs t1 t2 -> Rew lhs rhs t2 t3 -> Rew lhs rhs t1 t3
| Rew_App_l : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r))}
                     {C : Con B}
                     {A B : Ty B}
                     {f1 f2 : Tm ar C (A ⟶ B)}
                     (x : Tm ar C A),
    Rew lhs rhs f1 f2 -> Rew lhs rhs (f1 · x) (f2 · x)
| Rew_App_r : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r))}
                     {C : Con B}
                     {A B : Ty B}
                     (f : Tm ar C (A ⟶ B))
                     {x1 x2 : Tm ar C A},
    Rew lhs rhs x1 x2 -> Rew lhs rhs (f · x1) (f · x2)
| Rew_Lam : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r))}
                   {C : Con B}
                   {A B : Ty B}
                   {f1 f2 : Tm ar (A ,, C) B},
    Rew lhs rhs f1 f2 -> Rew lhs rhs (λ f1) (λ f2)
| BaseRew : forall {lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r))}
                   {C : Con B}
                   (r : R)
                   (s : Sub ar C (Rcon r)),
    Rew lhs rhs (subTm (lhs r) s) (subTm (rhs r) s).
 *)

Definition beta_sub
           {B : Type}
           {F : Type}
           {ar : F -> Ty B}
           {C : Con B}
           {A : Ty B}
           (t : Tm ar C A)
  : Sub ar C (A ,, C)
  := ExtendSub (idSub C ar) t.

Inductive BetaRed
          {B : Type}
          {F : Type}
          {ar : F -> Ty B}
          {C : Con B}
  : forall {A : Ty B}, Tm ar C A -> Tm ar C A -> Prop
  :=
| BetaTrans : forall {A : Ty B}
                     {t1 t2 t3 : Tm ar C A},
    BetaRed t1 t2 -> BetaRed t2 t3 -> BetaRed t1 t3
| BetaRew_App_l : forall {A1 A2 : Ty B}
                         {f1 f2 : Tm ar C (A1 ⟶ A2)}
                         (x : Tm ar C A1),
    BetaRed f1 f2 -> BetaRed (f1 · x) (f2 · x)
| BetaRew_App_r : forall {A1 A2 : Ty B}
                         (f : Tm ar C (A1 ⟶ A2))
                         {x1 x2 : Tm ar C A1},
    BetaRed x1 x2 -> BetaRed (f · x1) (f · x2)
| BetaRew_Lam : forall {A1 A2 : Ty B}
                       {f1 f2 : Tm ar (A1 ,, C) A2},
    BetaRed f1 f2 -> BetaRed (λ f1) (λ f2)
| BetaBeta : forall {A1 A2 : Ty B}
                    (f : Tm ar (A1 ,, C) A2)
                    (x : Tm ar C A1),
    BetaRed ((λ f) · x) (subTm f (beta_sub x)).

Arguments BetaTrans {_ _ _ _} {_ _ _ _} _ _.
Arguments BetaRew_App_l {_ _ _ _} {_ _ _ _} _ _.
Arguments BetaRew_App_r {_ _ _ _} {_ _} _ {_ _} _.
Arguments BetaRew_Lam {_ _ _ _} {_ _ _ _} _.
Arguments BetaBeta {_ _ _ _} {_ _} _ _.

Inductive Rew
          {B : Type}
          {F : Type}
          {ar : F -> Ty B}
          {R : Type}
          {Rcon : R -> Con B}
          {Rtar : R -> B}
          (lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r)))
          {C : Con B}
  : forall {A : Ty B}, Tm ar C A -> Tm ar C A -> Prop
  :=
| Trans : forall {A : Ty B}
                 {t1 t2 t3 : Tm ar C A},
    Rew lhs rhs t1 t2 -> Rew lhs rhs t2 t3 -> Rew lhs rhs t1 t3
| Rew_App_l : forall {A1 A2 : Ty B}
                     {f1 f2 : Tm ar C (A1 ⟶ A2)}
                     (x : Tm ar C A1),
    Rew lhs rhs f1 f2 -> Rew lhs rhs (f1 · x) (f2 · x)
| Rew_App_r : forall {A1 A2 : Ty B}
                     (f : Tm ar C (A1 ⟶ A2))
                     {x1 x2 : Tm ar C A1},
    Rew lhs rhs x1 x2 -> Rew lhs rhs (f · x1) (f · x2)
| Rew_Lam : forall {A1 A2 : Ty B}
                   {f1 f2 : Tm ar (A1 ,, C) A2},
    Rew lhs rhs f1 f2 -> Rew lhs rhs (λ f1) (λ f2)
| Beta : forall {A1 A2 : Ty B}
                (f : Tm ar (A1 ,, C) A2)
                (x : Tm ar C A1),
    Rew lhs rhs ((λ f) · x) (subTm f (beta_sub x))
| BaseRew : forall (r : R)
                   (s : Sub ar C (Rcon r)),
    Rew lhs rhs (subTm (lhs r) s) (subTm (rhs r) s).

Arguments Trans {_ _ _ _ _ _ _ _ _} {_ _ _ _} _ _.
Arguments Rew_App_l {_ _ _ _ _ _ _ _ _} {_ _ _ _} _ _.
Arguments Rew_App_r {_ _ _ _ _ _ _ _ _} {_ _} _ {_ _} _.
Arguments Rew_Lam {_ _ _ _ _ _ _ _ _} {_ _ _ _} _.
Arguments Beta {_ _ _ _ _ _ _ _ _} {_ _} _ _.
Arguments BaseRew {_ _ _ _ _ _ _ _ _} _ _.
