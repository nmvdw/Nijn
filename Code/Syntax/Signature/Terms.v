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
| Lam : forall (ar : F -> Ty B) (C : Con B) (A1 A2 : Ty B),
    Tm ar (A1 ,, C) A2 -> Tm ar C (A1 ⟶ A2)
| App : forall (ar : F -> Ty B) (C : Con B) (A1 A2 : Ty B),
    Tm ar C (A1 ⟶ A2) -> Tm ar C A1 -> Tm ar C A2.

Arguments BaseTm {_} {_} {_} {_} _.
Arguments TmVar {_} {_} {_} {_} {_} _.
Arguments Lam {_} {_} {_} {_} {_} {_} _.
Arguments App {_} {_} {_} {_} {_} {_} _ _.

Notation "'λ' x" := (Lam x) (at level 10) : signature.
Notation "f · x" := (App f x) (at level 20, left associativity) : signature.
