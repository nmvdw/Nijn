Require Import Nijn.Syntax.Signature.
Require Import Nijn.TerminationTechniques.PolynomialMethod.Polynomial.

Declare Scope poly_scope.
Open Scope poly_scope.

(** * Overloaded notations for polynomials *)

(** We introduce notation for polynomials so that using them becomes more convenient. When using oolynomials, one often regularly needs to perform addition/multiplication on polynomials of different types, and the goal here is to have a uniform notation for all of these operations *)

(** ** Notation for addition *)
Class addClass (A B C : Type) :=
  addFun : A -> B -> C.

Notation "P1 + P2" := (addFun P1 P2) : poly_scope.

Global Instance add_base_base {B : Type} (C : con B)
  : addClass (base_poly C) (base_poly C) (base_poly C)
  := fun P1 P2 => P_plus P1 P2.
  
Global Instance add_base_poly {B : Type} (C : con B) (b : B)
  : addClass (base_poly C) (poly C (Base b)) (base_poly C)
  := fun P1 P2 => P1 + from_poly P2.

Global Instance add_poly_base {B : Type} (C : con B) (b : B)
  : addClass (poly C (Base b)) (base_poly C) (base_poly C)
  := fun P1 P2 => from_poly P1 + P2.

Global Instance add_poly_poly {B : Type} (C : con B) (b1 b2 : B)
  : addClass (poly C (Base b1)) (poly C (Base b2)) (base_poly C)
  := fun P1 P2 => from_poly P1 + from_poly P2.

(** ** Notation for multiplication *)
Class multClass (A B C : Type) :=
  multFun : A -> B -> C.

Notation "P1 * P2" := (multFun P1 P2) : poly_scope.

Global Instance mult_base_base {B : Type} (C : con B)
  : multClass (base_poly C) (base_poly C) (base_poly C)
  := fun P1 P2 => P_mult P1 P2.

Global Instance mult_base_poly {B : Type} (C : con B) (b : B)
  : multClass (base_poly C) (poly C (Base b)) (base_poly C)
  := fun P1 P2 => P1 * from_poly P2.

Global Instance mult_poly_base {B : Type} (C : con B) (b : B)
  : multClass (poly C (Base b)) (base_poly C) (base_poly C)
  := fun P1 P2 => from_poly P1 * P2.

Global Instance mult_poly_poly {B : Type} (C : con B) (b1 b2 : B)
  : multClass (poly C (Base b1)) (poly C (Base b2)) (base_poly C)
  := fun P1 P2 => from_poly P1 * from_poly P2.

(** ** Notation for application *)
Class appClass (A B C : Type) :=
  appFun : A -> B -> C.

Notation "P1 ·P P2" := (appFun P1 P2) (at level 20) : poly_scope.

Global Instance app_poly_poly {B : Type} (C : con B) (A1 A2 : ty B)
  : appClass (poly C (A1 ⟶ A2)) (poly C A1) (poly C A2)
  := fun P1 P2 => P_app P1 P2.

Global Instance app_poly_base {B : Type} (C : con B) (A : ty B) (b : B)
  : appClass (poly C (A ⟶ Base b)) (poly C A) (base_poly C)
  := fun P1 P2 => from_poly (P1 ·P P2).

Global Instance app_base_base {B : Type} (C : con B) (b1 b2 b3 : B)
  : appClass (poly C (Base b1 ⟶ Base b2)) (poly C (Base b3)) (base_poly C)
  := fun P1 P2 => P1 ·P P_base (from_poly P2).

Global Instance app_base_base_alt {B : Type} (C : con B) (b1 b2 : B)
  : appClass (poly C (Base b1 ⟶ Base b2)) (base_poly C) (base_poly C)
  := fun P1 P2 => P1 ·P @P_base _ _ b2 P2.

Global Instance app_base_base_alt' {B : Type} (C : con B) (b1 : B) (A : ty B)
  : appClass (poly C (Base b1 ⟶ A)) (base_poly C) (poly C A)
  := fun P1 P2 => P_app P1 (P_base P2).

Global Instance app_base_poly {B : Type} (C : con B) (b1 b2 : B) (A : ty B)
  : appClass (poly C (Base b1 ⟶ A)) (poly C (Base b2)) (poly C A)
  := fun P1 P2 => P_app P1 (P_base (from_poly P2)).

Global Instance app_base_base_poly {B : Type} (C : con B) (b1 b2 : B) (A : ty B)
  : appClass (poly C (Base b1 ⟶ A)) (base_poly C ) (poly C A)
  := fun P1 P2 => P_app P1 (P_base P2).

Notation "'λP' P" := (P_lam P) (at level 10) : poly_scope.

Class toPoly (X : Type) {B : Type} (C : con B) (A : ty B) :=
  to_Poly : X -> poly C A.

Global Instance base_poly_toPoly {B : Type} (C : con B) (b : B)
  : toPoly (base_poly C) C (Base b)
  := fun P => P_base P.

Global Instance poly_toPoly {B : Type} (C : con B) (A : ty B)
  : toPoly (poly C A) C A
  := fun P => P.

Global Instance poly_base_toPoly {B : Type} (C : con B) (b₁ b₂ : B)
  : toPoly (poly C (Base b₁)) C (Base b₂)
  := fun P => P_base (from_poly P).
