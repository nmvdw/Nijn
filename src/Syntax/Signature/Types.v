Require Import Nijn.Prelude.

Declare Scope signature.
Open Scope signature.

(** * Definition of simple types in an AFS *)

(** Notational convention: we use [B] for the collection of base types, and simple types are named [A, A1, ...] *)

Inductive ty (B : Type) : Type :=
| Base : B -> ty B
| Fun : ty B -> ty B -> ty B.

Arguments Base {_} _.
Arguments Fun {_} _ _.
Notation "A ⟶ B" := (Fun A B) (at level 70, right associativity) : signature.

(** ** Decidable equality of types *)

(** Lemmata on equality of the constructors *)
Proposition Base_nequal
            {B : Type}
            {b1 b2 : B}
            (p : b1 <> b2)
  : Base b1 <> Base b2.
Proof.
  intro q.
  inversion q.
  contradiction.
Qed.

Proposition Base_not_Fun
            {B : Type}
            {A1 A2 : ty B}
            {b : B}
  : Base b <> (A1 ⟶ A2).
Proof.
  discriminate.
Qed.

Proposition Fun_not_Base
            {B : Type}
            {A1 A2 : ty B}
            {b : B}
  : (A1 ⟶ A2) <> Base b.
Proof.
  discriminate.
Qed.

Proposition eq_Fun
            {B : Type}
            {A1 A2 A3 A4 : ty B}
            (p : A1 = A3)
            (q : A2 = A4)
  : (A1 ⟶ A2) = (A3 ⟶ A4).
Proof.
  subst.
  reflexivity.
Qed.

Proposition neq_Fun₁
            {B : Type}
            {A1 A2 A3 A4 : ty B}
            (p : A1 <> A3)
  : (A1 ⟶ A2) <> (A3 ⟶ A4).
Proof.
  intro q.
  inversion q.
  contradiction.
Qed.

Proposition neq_Fun₂
            {B : Type}
            {A1 A2 A3 A4 : ty B}
            (p : A2 <> A4)
  : (A1 ⟶ A2) <> (A3 ⟶ A4).
Proof.
  intro q.
  inversion q.
  contradiction.
Qed.

(** The function that decides equality *)
Fixpoint dec_eq_Ty
         {B : Type}
         `{decEq B}
         (A1 A2 : ty B)
  : dec (A1 = A2)
  := match A1 , A2 with
     | Base b1 , Base b2 =>
       match dec_eq b1 b2 with
       | Yes p => Yes (f_equal Base p)
       | No p => No (Base_nequal p)
       end
     | A1 ⟶ A2 , A3 ⟶ A4 =>
       match dec_eq_Ty A1 A3 with
       | Yes p =>
         match dec_eq_Ty A2 A4 with
         | Yes q => Yes (eq_Fun p q)
         | No q => No (neq_Fun₂ q)
         end
       | No p => No (neq_Fun₁ p)
       end
     | _ ⟶ _ , Base _ => No Fun_not_Base
     | Base _ , _ ⟶ _ => No Base_not_Fun
     end.

Global Instance decEq_Ty
       {B : Type}
       `{decEq B}
  : decEq (ty B)
  := {| dec_eq := dec_eq_Ty |}.
