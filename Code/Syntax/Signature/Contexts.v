Require Import Prelude.Basics.
Require Import Types.
Require Import Coq.Program.Equality.
Require Import Eqdep.

(** * Contexts *)

Inductive con (B : Type) : Type :=
| Empty : con B
| Extend : ty B -> con B -> con B.

Arguments Empty {_}.
Arguments Extend {_} _ _.

Notation "∙" := Empty : signature.
Notation "A ,, Γ" := (Extend A Γ) (at level 70, right associativity) : signature.

(** * Variables *)

(** Note: we represent variables using De Bruijn indices *)
Inductive var {B : Type} : con B -> ty B -> Type :=
| Vz : forall (C : con B) (A : ty B),
    var (A ,, C) A
| Vs : forall (C : con B) (A1 A2 : ty B),
    var C A2 -> var (A1 ,, C) A2.

Arguments Vz {_} {_} {_}.
Arguments Vs {_} {_} {_} {_} _.

(** * Decidable equality of variables *)

(** We decide equality of variables by mapping them to the natural numbers and then deciding equality of the natural numbers. *)
Fixpoint var_to_nat
         {B : Type}
         {C : con B}
         {A : ty B}
         (v : var C A)
  : nat
  := match v with
     | Vz => 0
     | Vs v => S(var_to_nat v)
     end.

Proposition var_tonat_eq
            {B : Type}
            {C : con B}
            {A : ty B}
            {v1 v2 : var C A}
            (p : var_to_nat v1 = var_to_nat v2)
  : v1 = v2.
Proof.
  induction v1.
  - dependent destruction v2.
    + reflexivity.
    + cbn in p.
      discriminate.
  - dependent destruction v2.
    + simpl in p.
      discriminate.
    + f_equal.
      apply IHv1.
      simpl in p.
      inversion p.
      reflexivity.
Qed.

Definition dec_eq_Var
        {B : Type}
        {C : con B}
        {A : ty B}
        (v1 v2 : var C A)
  : dec (v1 = v2)
  := match dec_eq (var_to_nat v1) (var_to_nat v2) with
     | Yes p => Yes (var_tonat_eq p)
     | No p => No (fun q => p (f_equal _ q))
     end.

Global Instance decEq_Var
       {B : Type}
       {C : con B}
       {A : ty B}
  : decEq (var C A)
  := {| dec_eq := dec_eq_Var |}.
