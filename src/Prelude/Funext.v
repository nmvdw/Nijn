Require Import Nijn.Prelude.Checks.
Require Export ProofIrrelevance.
Require Import Coq.Logic.FunctionalExtensionality.

(** * Functional extensionality *)

(** In this formalization, we assume functional extensionality. For that, we use the following abbreviation.
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

(** We also assume proof irrelevance for propositions. As a consequence, we have uniqueness of identity proofs (UIP). UIP says that all proofs of `a1 = a2` are equal. *)
Proposition UIP : forall {A : Type} {a1 a2 : A} (p q : a1 = a2), p = q.
Proof.
  intros.
  apply proof_irrelevance.
Qed.
