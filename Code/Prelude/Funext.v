Require Import Coq.Logic.FunctionalExtensionality.

(** Abbreviation for functional extensionality *)
Definition funext
           {A : Type}
           {B : A -> Type}
           {f g : forall (a : A), B a}
           (p : forall (a : A), f a = g a)
  : f = g.
Proof.
  apply functional_extensionality_dep.
  exact p.
Qed.
