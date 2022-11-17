Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Nijn.Interpretation.OrderInterpretation.
Require Import Nijn.TerminationTechniques.PolynomialMethod.
Require Import List.

(** * Strong normalization for the trivial AFS *)

(** The AFS without any rewrite rules is strongly normalizing. We prove that using the polynomial method. All function symbols are interpreted as the polynomial that is constantly 0. This is sufficient to conclude strong normalization, because there are no rewrite rules*)
Fixpoint zero_poly
         {B : Type}
         (A : ty B)
  : forall (C : con B), poly C A
  := match A with
     | Base _ => fun _ => P_base (P_const 0)
     | A₁ ⟶ A₂ => fun _ => λP (zero_poly A₂ _)
     end.

Theorem no_rules_SN
        {B F : Type}
        (X : afs B F)
        (H : rewriteRules X -> False)
  : isSN X.
Proof.
  apply afs_is_SN_from_Interpretation.
  simple refine (poly_Interpretation _ _ _).
  - intro f.
    apply zero_poly.
  - intro r.
    contradiction.
Defined.
    
Proposition empty_list_SN
            {B F : Type}
            (X : afs B F)
            (HX : isNil (list_of_rewriteRules X))
  : isSN X.
Proof.
  apply no_rules_SN.
  intro r.
  destruct r as [ r Hr ].
  pose (isNil_no_member _ HX r Hr).
  contradiction.
Qed.
