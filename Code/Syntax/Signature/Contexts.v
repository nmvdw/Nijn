Require Import Types.

Inductive Con (B : Type) : Type :=
| Empty : Con B
| Extend : Ty B -> Con B -> Con B.

Arguments Empty {_}.
Arguments Extend {_} _ _.

Notation "∙" := Empty : signature.
Notation "A ,, Γ" := (Extend A Γ) (at level 70, right associativity) : signature.

Inductive Var {B : Type} : Con B -> Ty B -> Type :=
| Vz : forall (C : Con B) (A : Ty B),
    Var (A ,, C) A
| Vs : forall (C : Con B) (A1 A2 : Ty B),
    Var C A2 -> Var (A1 ,, C) A2.

Arguments Vz {_} {_} {_}.
Arguments Vs {_} {_} {_} {_} _.
