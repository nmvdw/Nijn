Require Import Nijn.Prelude.Checks.
Require Import Nijn.Prelude.Funext.
Require Import Nijn.Prelude.Relations.WellfoundedRelation.
Require Import Nijn.Prelude.Orders.CompatibleRelation.

(** * Monotone maps *)

(** We have two kinds of structure preserving maps between compatible relations. First of all, we can look at strictly monotone maps, which preserve the strict order. *)
Class strictMonotone {X Y : CompatRel} (f : X -> Y) :=
  map_gt : forall (x y : X),
    x > y -> f x > f y.

(** Second of all, we can look at weak monotone maps, which preserve the other order *)
Class weakMonotone {X Y : CompatRel} (f : X -> Y) :=
  map_ge : forall (x y : X),
    x >= y -> f x >= f y.

(** Now we define the type of weakly and strongly monotone maps between compatible relations *)
Record weakMonotoneMap (X Y : CompatRel) :=
  make_monotone
    {
      fun_carrier :> X -> Y ;
      is_weak_monotone : weakMonotone fun_carrier
    }.

Arguments make_monotone {_ _} _ _.

Global Instance weakMonotoneMap_isWeakMonotone
       {X Y : CompatRel}
       (f : weakMonotoneMap X Y)
  : weakMonotone f
  := is_weak_monotone _ _ f.

Record strongMonotoneMap (X Y : CompatRel) :=
  make_strong_monotone
    {
      strong_fun_carrier :> X -> Y ;
      strong_is_weak : weakMonotone strong_fun_carrier ;
      strong_is_strict : strictMonotone strong_fun_carrier ;
    }.

Arguments make_strong_monotone {_ _} _ _ _.

Global Instance strongMonotone_to_strictMonotone
                {X Y : CompatRel}
                (f : strongMonotoneMap X Y)
  : strictMonotone f
  := strong_is_strict _ _ f.

Global Instance strongMonotone_to_weakMonotone
                {X Y : CompatRel}
                (f : strongMonotoneMap X Y)
  : weakMonotone f
  := strong_is_weak _ _ f.

(** ** Equality of monotone maps *)

(** Using function extensionality and proof irrelevance, we can show that monotone maps are equal if they are pointwise equal. *)
Definition eq_weakMonotoneMap_help
           {X Y : CompatRel}
           `{isCompatRel Y}
           (f g : weakMonotoneMap X Y)
           (p : fun_carrier _ _ f = fun_carrier _ _ g)
  : f = g.
Proof.
  destruct f as [f Hf].
  destruct g as [g Hg].
  cbn in p.
  revert Hf Hg.
  rewrite p.
  intros Hf Hg.
  f_equal.
  apply proof_irrelevance.
Qed.

Definition eq_weakMonotoneMap
           {X Y : CompatRel}
           `{isCompatRel Y}
           (f g : weakMonotoneMap X Y)
           (p : forall (x : X), f x = g x)
  : f = g.
Proof.
  apply eq_weakMonotoneMap_help.
  apply funext.
  exact p.
Qed.

Definition eq_strongMonotoneMap_help
           {X Y : CompatRel}
           `{isCompatRel Y}
           (f g : strongMonotoneMap X Y)
           (p : strong_fun_carrier _ _ f = strong_fun_carrier _ _ g)
  : f = g.
Proof.
  destruct f as [ f Hf1 Hf2 ].
  destruct g as [ g Hg1 Hg2 ].
  cbn in p.
  revert Hf1 Hf2 Hg1 Hg2.
  rewrite p.
  intros Hf1 Hf2 Hg1 Hg2.
  f_equal ; apply proof_irrelevance.
Qed.

Definition eq_strongMonotoneMap
           {X Y : CompatRel}
           `{isCompatRel Y}
           (f g : strongMonotoneMap X Y)
           (p : forall (x : X), f x = g x)
  : f = g.
Proof.
  apply eq_strongMonotoneMap_help.
  apply funext.
  exact p.
Qed.

