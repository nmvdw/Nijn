Require Import Coq.Logic.FunctionalExtensionality.

(** * Functional extensionality *)

(** In most of this formalization, we assume functional extensionality. For that, we use the following abbreviation.
 *)
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

(** * UIP *)

(* We also assume UIP *)
Axiom UIP : forall {A : Type} {a1 a2 : A} (p q : a1 = a2), p = q.
