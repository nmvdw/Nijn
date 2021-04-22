Require Import Prelude.Funext.
Require Import Coq.Program.Equality.
Require Import Lia.

(** * Propositional types *)

(** A type is called a proposition if all its elements are equal *)
Class isaprop
      (A : Prop)
  := all_eq : forall (x y : A), x = y.

(** False is a proposition *)
Global Instance False_isaprop : isaprop False.
Proof.
  intro ; contradiction.
Qed.

(** True is a proposition *)
Global Instance True_isaprop : isaprop True.
Proof.
  intros x y.
  destruct x, y.
  reflexivity.
Qed.

(** Propositions are closed under conjunction *)
Global Instance and_isaprop
       {A B : Prop}
       `{isaprop A}
       `{isaprop B}
  : isaprop (A /\ B).
Proof.
  intros x y.
  destruct x as [a1 b1], y as [a2 b2].
  rewrite (all_eq a1 a2).
  rewrite (all_eq b1 b2).
  reflexivity.
Qed.

(** Assuming functional extensionality, propositions are closed under dependent products *)
Global Instance forall_isaprop
       {X : Type}
       {B : X -> Prop}
       `{forall (x : X), isaprop (B x)}
  : isaprop (forall (x : X), B x).
Proof.
  intros f g.
  apply funext.
  intro x.
  apply all_eq.
Qed.

(** The order on natural numbers is a proposition *)
Global Instance nat_le_isaprop
       (n m : nat)
  : isaprop (n <= m).
Proof.
  unfold isaprop.
  induction m ; intros p q.
  - dependent destruction p ; dependent destruction q.
    reflexivity.
  - dependent destruction p ; dependent destruction q.
    + reflexivity.
    + lia.
    + lia.
    + f_equal.
      exact (IHm p q).
Qed.

Global Instance nat_gt_isaprop
       (n m : nat)
  : isaprop (n > m)
  := _.

Global Instance nat_ge_isaprop
       (n m : nat)
  : isaprop (n >= m)
  := _.
