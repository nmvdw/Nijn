Require Import Prelude.Funext.
Require Import Lia.
Require Import Coq.Program.Equality.

Declare Scope compat.
Open Scope compat.

(** MOVE TO FILE ON BASICS *)
Class isaprop
      (A : Prop)
  := all_eq : forall (x y : A), x = y.

Global Instance False_isaprop : isaprop False.
Proof.
  intro ; contradiction.
Qed.

Global Instance True_isaprop : isaprop True.
Proof.
  intros x y.
  destruct x, y.
  reflexivity.
Qed.

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

(** END MOVE *)

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

Class isCompatRel (X : CompatRel) :=
  {
    gt_trans : forall {x y z : X},
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
      x > y -> y >= z -> x > z ;
    gt_prop : forall (x y : X),
      isaprop (x > y) ;
    ge_prop : forall (x y : X),
      isaprop (x >= y)
  }.

Global Instance gt_isaprop
       (X : CompatRel)
       `{isCompatRel X}
       (x y : X)
  : isaprop (x > y)
  := gt_prop x y.

Global Instance ge_isaprop
       (X : CompatRel)
       `{isCompatRel X}
       (x y : X)
  : isaprop (x >= y)
  := ge_prop x y.

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

Definition unit_CompatRel : CompatRel
  := {| carrier := unit ;
        gt := fun _ _ => False ;
        ge := fun _ _ => True |}.

Global Instance unit_isCompatRel : isCompatRel unit_CompatRel.
Proof.
  unshelve esplit ; cbn ; auto ; apply _.
Qed.

Definition prod_CompatRel
           (X Y : CompatRel)
  : CompatRel
  := {| carrier := X * Y ;
        gt := fun x y => (fst x > fst y) /\ (snd x > snd y) ;
        ge := fun x y => (fst x >= fst y) /\ (snd x >= snd y) |}.

Notation "X * Y" := (prod_CompatRel X Y) : compat.

Global Instance prod_isCompatRel
       (X Y : CompatRel)
       `{isCompatRel X}
       `{isCompatRel Y}
  : isCompatRel (X * Y).
Proof.
  unshelve esplit ; cbn ; try (intros ; apply _).
  - intros x y z p q ; split.
    + refine (gt_trans _ _).
      * apply p.
      * apply q.
    + refine (gt_trans _ _).
      * apply p.
      * apply q.
  - intros x y z p q ; split.
    + refine (ge_trans _ _).
      * apply p.
      * apply q.
    + refine (ge_trans _ _).
      * apply p.
      * apply q.
  - intros x ; split ; apply ge_refl.
  - intros x y p ; split ; apply compat ; apply p.
  - intros x y z p q.
    split.
    + refine (ge_gt _ _).
      * apply p.
      * apply q.
    + refine (ge_gt _ _).
      * apply p.
      * apply q.
  - intros x y z p q.
    split.
    + refine (gt_ge _ _).
      * apply p.
      * apply q.
    + refine (gt_ge _ _).
      * apply p.
      * apply q.
Qed.

Definition depprod_CompatRel
           {X : Type}
           (Y : X -> CompatRel)
  : CompatRel
  := {| carrier :=  (forall (x : X), Y x) ;
        gt := fun f g => forall (x : X), f x > g x ;
        ge := fun f g => forall (x : X), f x >= g x |}.

Notation "∏ Y" := (depprod_CompatRel Y) (at level 10).

Global Instance depprod_isCompatRel
           {X : Type}
           (Y : X -> CompatRel)
           `{forall (x : X), isCompatRel (Y x)}
  : isCompatRel (∏ Y).
Proof.
  unshelve esplit ; cbn ; try (intros ; apply _).
  - intros f g h p q x.
    exact (gt_trans (p x) (q x)).
  - intros f g h p q x.
    exact (ge_trans (p x) (q x)).
  - intros f x.
    exact (ge_refl (f x)).
  - intros f g p x.
    exact (compat (p x)).
  - intros f g h p q x.
    exact (ge_gt (p x) (q x)).
  - intros f g h p q x.
    exact (gt_ge (p x) (q x)).
Qed.

Fixpoint power_CompatRel
         (X : CompatRel)
         (n : nat)
  : CompatRel
  := match n with
     | 0 => unit_CompatRel
     | S n => X * power_CompatRel X n
     end.

Notation "X ^ n" := (power_CompatRel X n).

Global Instance power_isCompatRel
       (X : CompatRel)
       (n : nat)
       `{isCompatRel X}
  : isCompatRel (X ^ n).
Proof.
  induction n as [ | n IHn ] ; cbn.
  - apply _.
  - apply _.
Qed.

Definition nat_CompatRel
  : CompatRel
  := {| carrier := nat ;
        gt := fun n m => n > m ;
        ge := fun n m => n >= m |}%nat.

Global Instance nat_isCompatRel
  : isCompatRel nat_CompatRel.
Proof.
  unshelve esplit ; cbn ; intros ; try lia ; try (apply _).
Qed.

Class strictMonotone {X Y : CompatRel} (f : X -> Y) :=
  map_gt : forall (x y : X),
    x > y -> f x > f y.

Global Instance strictMonotone_isaprop
       {X Y : CompatRel}
       `{isCompatRel Y}
       (f : X -> Y)
  : isaprop (strictMonotone f).
Proof.
  unfold strictMonotone.
  apply _.
Qed.

Class weakMonotone {X Y : CompatRel} (f : X -> Y) :=
  map_ge : forall (x y : X),
    x >= y -> f x >= f y.

Global Instance weakMonotone_isaprop
       {X Y : CompatRel}
       `{isCompatRel Y}
       (f : X -> Y)
  : isaprop (weakMonotone f).
Proof.
  unfold weakMonotone.
  apply _.
Qed.

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

Definition fun_CompatRel
           (X Y : CompatRel)
  : CompatRel
  := {| carrier := weakMonotoneMap X Y ;
        gt := fun f g => forall (x : X), f x > g x ;
        ge := fun f g => forall (x : X), f x >= g x  |}.

Notation "X ⇒ Y" := (fun_CompatRel X Y) (at level 99).

Global Instance fun_isCompatRel
       (X Y : CompatRel)
       `{isCompatRel Y}
  : isCompatRel (X ⇒ Y).
Proof.
  unshelve esplit ; cbn ; try (intros ; apply _).
  - intros f g h p q x.
    exact (gt_trans (p x) (q x)).
  - intros f g h p q x.
    exact (ge_trans (p x) (q x)).
  - intros f x.
    exact (ge_refl (f x)).
  - intros f g p x.
    exact (compat (p x)).
  - intros f g h p q x.
    exact (ge_gt (p x) (q x)).
  - intros f g h p q x.
    exact (gt_ge (p x) (q x)).
Qed.

Global Instance const_weakMonotone
       (X Y : CompatRel)
       `{isCompatRel Y}
       (y : Y)
  : weakMonotone (fun (_ : X) => y).
Proof.
  intros x1 x2 p.
  apply ge_refl.
Qed.

Definition const_WM
           (X Y : CompatRel)
           `{isCompatRel Y}
           (y : Y)
  : X ⇒ Y
  := make_monotone (fun (_ : X) => y) _.

Definition id {X : Type} (x : X) := x.
Arguments id {_} _/.


Global Instance id_strictMonotone (X : CompatRel)
  : strictMonotone (@id X).
Proof.
  intros x y p.
  exact p.
Qed.

Global Instance id_weakMonotone (X : CompatRel)
  : weakMonotone (@id X).
Proof.
  intros x y p.
  exact p.
Qed.

Definition id_WM
           (X : CompatRel)
  : X ⇒ X
  := make_monotone id _.

Definition comp
           {X Y Z : Type}
           (g : Y -> Z)
           (f : X -> Y)
           (x : X)
  : Z
  := g(f x).

Notation "g 'o' f" := (comp g f) (at level 40, left associativity).
Arguments comp {_ _ _} _ _ _/.

Global Instance comp_strictMonotone
       {X Y Z : CompatRel}
       (f : X -> Y)
       (g : Y -> Z)
       `{strictMonotone _ _ f}
       `{strictMonotone _ _ g}
  : strictMonotone (g o f).
Proof.
  intros x y p ; cbn.
  do 2 apply map_gt.
  assumption.
Qed.

Global Instance comp_weakMonotone
       {X Y Z : CompatRel}
       (f : X -> Y)
       (g : Y -> Z)
       `{weakMonotone _ _ f}
       `{weakMonotone _ _ g}
  : weakMonotone (g o f).
Proof.
  intros x y p ; cbn.
  do 2 apply map_ge.
  assumption.
Qed.

Definition comp_WM
           {X Y Z : CompatRel}
           (f : X ⇒ Y)
           (g : Y ⇒ Z)
  : X ⇒ Z
  := make_monotone (g o f) _.

Global Instance fst_strictMonotone
       {X Y : CompatRel}
  : @strictMonotone (X * Y) X fst.
Proof.
  intros x y p.
  apply p.
Qed.

Global Instance fst_weakMonotone
       {X Y : CompatRel}
  : @weakMonotone (X * Y) X fst.
Proof.
  intros x y p.
  apply p.
Qed.

Definition fst_WM
           (X Y : CompatRel)
  : (X * Y) ⇒ X
  := make_monotone _ _.

Global Instance snd_strictMonotone
       {X Y : CompatRel}
  : @strictMonotone (X * Y) Y snd.
Proof.
  intros x y p.
  apply p.
Qed.

Global Instance snd_weakMonotone
       {X Y : CompatRel}
  : @weakMonotone (X * Y) Y snd.
Proof.
  intros x y p.
  apply p.
Qed.

Definition snd_WM
           (X Y : CompatRel)
  : (X * Y) ⇒ Y
  := make_monotone _ _.

Global Instance pair_weakMonotone
       {X Y Z : CompatRel}
       (f : X -> Y)
       (g : X -> Z)
       `{weakMonotone _ _ f}
       `{weakMonotone _ _ g}
  : @weakMonotone X (Y * Z) (fun x => (f x , g x)).
Proof.
  intros x y p.
  split.
  - simpl.
    apply map_ge.
    assumption.
  - simpl.
    apply map_ge.
    assumption.
Qed.

Global Instance pair_strictMonotone
       {X Y Z : CompatRel}
       (f : X -> Y)
       (g : X -> Z)
       `{strictMonotone _ _ f}
       `{strictMonotone _ _ g}
  : @strictMonotone X (Y * Z) (fun x => (f x , g x)).
Proof.
  intros x y p.
  split.
  - simpl.
    apply map_gt.
    assumption.
  - simpl.
    apply map_gt.
    assumption.
Qed.

Definition pair_WM
           {X Y Z : CompatRel}
           (f : X ⇒ Y)
           (g : X ⇒ Z)
  : X ⇒ (Y * Z)
  := @make_monotone X (Y * Z) (fun x => (f x , g x)) _.

Global Instance lambda_abs_on_X_monotone
       {X Y Z : CompatRel}
       `{isCompatRel X}
       (f : X * Y ⇒ Z)
       (x : X)
  : weakMonotone (fun y => f (x , y)).
Proof.
  intros z1 z2 p.
  apply map_ge.
  split.
  - apply ge_refl.
  - exact p.
Qed.

Definition lambda_abs_on_X
           {X Y Z : CompatRel}
           `{isCompatRel X}
           (f : Y * X ⇒ Z)
           (x : X)
  : Y ⇒ Z
  := make_monotone (fun y => f (y , x)) _.

Global Instance lambda_abs_mon
       {X Y Z : CompatRel}
       `{isCompatRel X}
       `{isCompatRel Y}
       (f : X * Y ⇒ Z)
  : weakMonotone (fun x => lambda_abs_on_X f x).
Proof.
  intros x y p z ; cbn.
  apply map_ge.
  split.
  - apply ge_refl.
  - exact p.
Qed.

Definition lambda_abs
       {X Y Z : CompatRel}
       `{isCompatRel X}
       `{isCompatRel Y}
       (f : Y * X ⇒ Z)
  : X ⇒ (Y ⇒ Z)
  := make_monotone (fun x : X => lambda_abs_on_X f x) _.

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
  apply all_eq.
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
