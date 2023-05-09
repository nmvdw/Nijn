Require Import List.

Ltac solve_In :=
  cbn -[In] ;
  match goal with
  | [ |- In ?x (?x :: _) ] => left ; reflexivity
  | [ |- In ?x (?y :: _) ] => right ; solve_In
  | [ |- In _ nil ] => fail
  end.
