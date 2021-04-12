Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.

Open Scope signature.

Inductive Tm {B : Type} {F : Type}
  : (F -> Ty B) -> Con B -> Ty B -> Type
  :=
| BaseTm : forall (ar : F -> Ty B) (C : Con B) (f : F),
    Tm ar C (ar f)
| TmVar : forall (ar : F -> Ty B) (C : Con B) (A : Ty B),
    Var C A -> Tm ar C A
| Lam : forall (ar : F -> Ty B) (C : Con B) (A₁ A₂ : Ty B),
    Tm ar (A₁ ,, C) A₂ -> Tm ar C (A₁ ⟶ A₂)
| App : forall (ar : F -> Ty B) (C : Con B) (A₁ A₂ : Ty B),
    Tm ar C (A₁ ⟶ A₂) -> Tm ar C A₁ -> Tm ar C A₂.

Arguments BaseTm {_} {_} {_} {_} _.
Arguments TmVar {_} {_} {_} {_} {_} _.
Arguments Lam {_} {_} {_} {_} {_} {_} _.
Arguments App {_} {_} {_} {_} {_} {_} _ _.

Notation "'λ' x" := (Lam x) (at level 10) : signature.
Notation "f · x" := (App f x) (at level 20, left associativity) : signature.
