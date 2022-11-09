Require Import Syntax.Signature.
Require Import Interpretation.Polynomial.

Declare Scope poly_scope.
Open Scope poly_scope.

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

Notation "'λP' P" := (P_lam P) (at level 10) : poly_scope.
