Require Import Nijn.Prelude.Checks.
Require Import Nijn.Prelude.Basics.Decidable.
Require Import Nijn.Prelude.Relations.WellfoundedRelation.

Declare Scope qr.
Open Scope qr.
Delimit Scope qr with qr.

(** * Quasi-orders *)
Record QuasiRel :=
  {
    carrier_qr :> Type ;
    ge_qr : carrier_qr -> carrier_qr -> Prop
  }.

Arguments ge_qr {_} _ _.

Notation "x >= y" := (ge_qr x y) : qr.

Class isQuasiRel ( X : QuasiRel ) :=
  {
    ge_qr_refl : forall (x : X),
      x >= x;
    ge_qr_trans : forall { x y z : X },
      x >= y -> y >= z -> x >= z
  }.

Close Scope qr.

(** * Compatible relations *)

Declare Scope compat.
Open Scope compat.
Delimit Scope compat with compat.
      
(** A compatible relation is a type equipped with two relations *)
Record CompatRel :=
  {
    carrier :> Type ;
    gt : carrier -> carrier -> Prop ;
    ge : carrier -> carrier -> Prop
  }.

Arguments gt {_} _ _.
Arguments ge {_} _ _.

Notation "x > y" := (gt x y) : compat.
Notation "x >= y" := (ge x y) : compat.

(** These are the axioms that should hold for compatible relations. Note that we do not require the relations to be well-founded, but that condition is formulated separately. *)
Class isCompatRel (X : CompatRel) :=
  {
    gt_trans : forall {x y z : carrier X},
      x > y -> y > z -> x > z ;
    ge_trans : forall {x y z : X},
      x >= y -> y >= z -> x >= z ;
    ge_refl : forall (x : X),
      x >= x ;
    compat : forall {x y : X},
      x > y -> x >= y ;
    ge_gt : forall {x y z : X},
      x >= y -> y > z -> x > z ;
    gt_ge : forall {x y z : X},
      x > y -> y >= z -> x > z
  }.

(** ** Lemmata for compatible relations *)
Proposition eq_gt
            {X : CompatRel}
            {x y z : X}
            (p : x = y)
            (q : y > z)
  : x > z.
Proof.
  induction p.
  exact q.
Qed.

Proposition gt_eq
            {X : CompatRel}
            {x y z : X}
            (p : x > y)
            (q : y = z)
  : x > z.
Proof.
  induction q.
  exact p.
Qed.

Proposition eq_ge
            {X : CompatRel}
            {x y z : X}
            (p : x = y)
            (q : y >= z)
  : x >= z.
Proof.
  induction p.
  exact q.
Qed.

Proposition ge_eq
            {X : CompatRel}
            {x y z : X}
            (p : x >= y)
            (q : y = z)
  : x >= z.
Proof.
  induction q.
  exact p.
Qed.

Proposition eq_to_ge
            {X : CompatRel}
            `{isCompatRel X}
            {x y : X}
            (p : x = y)
  : x >= y.
Proof.
  induction p.
  apply ge_refl.
Qed.

(** ** Minimal elements in a compatible relation *)
Definition is_minimal_element
           {X : CompatRel}
           (x : X)
  : Prop
  := forall (y : X), y >= x.

Record minimal_element (X : CompatRel) :=
  make_min_el
    {
      min_el :> X ;
      is_minimal : is_minimal_element min_el
    }.

Definition is_strict_minimal_element
           {X : CompatRel}
           (x : X)
  : Prop
  := forall (y : X), y <> x -> y > x.

Record strict_minimal_element (X : CompatRel) :=
  make_strict_min_el
    {
      strict_min_el :> X ;
      is_strict_minimal : is_strict_minimal_element strict_min_el
    }.

Definition is_minimal_to_strict_minimal
           {X : CompatRel}
           `{decEq X}
           `{isCompatRel X}
           (x : strict_minimal_element X)
  : minimal_element X.
Proof.
  simple refine (make_min_el _ _ _).
  - exact x.
  - intros y.
    destruct (dec_eq y x) as [ p | p ].
    + apply eq_to_ge.
      exact p.
    + exact (compat (is_strict_minimal _ x y p)).
Defined.
