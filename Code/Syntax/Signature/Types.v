Declare Scope signature.
Open Scope signature.

Inductive Ty (B : Type) : Type :=
| Base : B -> Ty B
| Fun : Ty B -> Ty B -> Ty B.

Arguments Base {_} _.
Arguments Fun {_} _ _.
Notation "A ⟶ B" := (Fun A B) (at level 70, right associativity) : signature.

(** Decidable equality of types *)
