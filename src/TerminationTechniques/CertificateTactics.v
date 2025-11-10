From Nijn Require Import TerminationTechniques.PolynomialMethod.
From Nijn Require Import TerminationTechniques.RuleRemoval.RuleSelector.
From Nijn Require Import TerminationTechniques.Certificate.
From Stdlib Require Import Lia.

Ltac nat_lt :=
  match goal with
  | [ n : nat |- _ ] => destruct n ; try (nia ; nat_lt)
  | _ => idtac
  end.

Ltac empty_certificate := apply EmptySN ; cbn ; auto.

Ltac poly_certificate pols :=
  match goal with
  | [ |- rule_removal_certificate ?X _ ] => apply (PolySRP X _ pols)
  | [ |- certificate _ ] => apply (PolySN _ pols)
  end ; solve_poly.

Ltac solve_included := abstract (cbn ; repeat split ; lia).

Ltac rule_removal_certificate rules :=
  simple refine (RuleRemovalSN _ (select_list_nats _ rules _) _ _) ;
  [ solve_included | | ].

Ltac certificate_SN := apply certificate_to_isSN.
