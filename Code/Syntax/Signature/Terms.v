Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.

Open Scope signature.

(** * Terms *)
Inductive tm {B : Type} {F : Type} (ar : F -> ty B) (C : con B) : ty B -> Type :=
| BaseTm : forall (f : F),
    tm ar C (ar f)
| TmVar : forall (A : ty B),
    var C A -> tm ar C A
| Lam : forall (A1 A2 : ty B),
    tm ar (A1 ,, C) A2 -> tm ar C (A1 ⟶ A2)
| App : forall (A1 A2 : ty B),
    tm ar C (A1 ⟶ A2) -> tm ar C A1 -> tm ar C A2.

Arguments BaseTm {_} {_} {_} {_} _.
Arguments TmVar {_} {_} {_} {_} {_} _.
Arguments Lam {_} {_} {_} {_} {_} {_} _.
Arguments App {_} {_} {_} {_} {_} {_} _ _.

Notation "'λ' x" := (Lam x) (at level 10) : signature.
Notation "f · x" := (App f x) (at level 20, left associativity) : signature.
