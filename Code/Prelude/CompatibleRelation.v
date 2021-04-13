Require Import Lia.

Declare Scope compat.
Open Scope compat.

Class CompatRel (X : Type) :=
  {
    gt : X -> X -> Prop ;
    ge : X -> X -> Prop
  }.

Arguments gt {_} {_} _ _.
Arguments ge {_} {_} _ _.

Notation "x > y" := (gt x y) : compat.
Notation "x >= y" := (ge x y) : compat.

Class isCompatRel (X : Type) `{CompatRel X} :=
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
      x > y -> y >= z -> x > z
  }.

Proposition eq_gt
            {X : Type}
            `{isCompatRel X}
            {x y z : X}
            (p : x = y)
            (q : y > z)
  : x > z.
Proof.
  induction p.
  exact q.
Qed.

Proposition gt_eq
            {X : Type}
            `{isCompatRel X}
            {x y z : X}
            (p : x > y)
            (q : y = z)
  : x > z.
Proof.
  induction q.
  exact p.
Qed.

Proposition eq_ge
            {X : Type}
            `{isCompatRel X}
            {x y z : X}
            (p : x = y)
            (q : y >= z)
  : x >= z.
Proof.
  induction p.
  exact q.
Qed.

Proposition ge_eq
            {X : Type}
            `{isCompatRel X}
            {x y z : X}
            (p : x >= y)
            (q : y = z)
  : x >= z.
Proof.
  induction q.
  exact p.
Qed.

Proposition eq_to_ge
            {X : Type}
            `{isCompatRel X}
            {x y : X}
            (p : x = y)
  : x >= y.
Proof.
  induction p.
  apply ge_refl.
Qed.

Global Instance unit_CompatRel : CompatRel unit
  := {| gt := fun _ _ => False ;
        ge := fun _ _ => True |}.

Global Instance unit_isCompatRel : isCompatRel unit.
Proof.
  unshelve esplit ; cbn ; auto.
Qed.

Global Instance prod_CompatRel
       (X Y : Type)
       `{CompatRel X}
       `{CompatRel Y}
  : CompatRel (X * Y)
  := {| gt := fun x y => (fst x > fst y) /\ (snd x > snd y) ;
        ge := fun x y => (fst x >= fst y) /\ (snd x >= snd y) |}.

Global Instance prod_isCompatRel
       (X Y : Type)
       `{isCompatRel X}
       `{isCompatRel Y}
  : isCompatRel (X * Y).
Proof.
  unshelve esplit ; cbn.
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

Global Instance depprod_CompatRel
       {X : Type}
       (Y : X -> Type)
       `{forall (x : X), CompatRel (Y x)}
  : CompatRel (forall (x : X), Y x)
  := {| gt := fun f g => forall (x : X), f x > g x ;
        ge := fun f g => forall (x : X), f x >= g x |}.

Global Instance depprod_isCompatRel
       {X : Type}
       (Y : X -> Type)
       `{forall (x : X), CompatRel (Y x)}
       `{forall (x : X), isCompatRel (Y x)}
  : isCompatRel (forall (x : X), Y x).
Proof.
  unshelve esplit ; cbn.
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

Global Instance fun_CompatRel
       (X Y : Type)
       `{CompatRel Y}
  : CompatRel (X -> Y)
  := _.

Global Instance fun_isCompatRel
       (X Y : Type)
       `{isCompatRel Y}
  : isCompatRel (X -> Y)
  := _.

Fixpoint power
         (X : Type)
         (n : nat)
  : Type
  := match n with
     | 0 => unit
     | S n => X * power X n
     end.

Notation "X ^ n" := (power X n) : compat.

Global Instance power_CompatRel
       (X : Type)
       (n : nat)
       `{CompatRel X}
  : CompatRel (X ^ n).
Proof.
  induction n as [ | n IHn ] ; cbn.
  - apply _.
  - apply _.
Defined.

Global Instance power_isCompatRel
       (X : Type)
       (n : nat)
       `{isCompatRel X}
  : isCompatRel (X ^ n).
Proof.
  induction n as [ | n IHn ] ; cbn.
  - apply _.
  - apply _.
Qed.

Global Instance nat_CompatRel
  : CompatRel nat
  := {| gt := fun n m => n > m ;
        ge := fun n m => n >= m |}%nat.

Global Instance nat_isCompatRel
  : isCompatRel nat.
Proof.
  unshelve esplit ; cbn ; intros ; lia.
Qed.

Class strictMonotone {X Y : Type} `{CompatRel X} `{CompatRel Y} (f : X -> Y) :=
  {
    map_gt : forall (x y : X),
      x > y -> f x > f y
  }.

Class weakMonotone {X Y : Type} `{CompatRel X} `{CompatRel Y} (f : X -> Y) :=
  {
    map_ge : forall (x y : X),
      x >= y -> f x >= f y
  }.

Global Instance const_weakMonotone
       (X Y : Type)
       `{CompatRel X}
       `{isCompatRel Y}
       (y : Y)
  : weakMonotone (fun (_ : X) => y).
Proof.
  unshelve esplit.
  intros.
  apply ge_refl.
Qed.

Definition id {X : Type} (x : X) := x.
Arguments id {_} _/.


Global Instance id_strictMonotone (X : Type) `{CompatRel X}
  : strictMonotone id.
Proof.
  unshelve esplit.
  intros x y p.
  exact p.
Qed.

Global Instance id_weakMonotone (X : Type) `{CompatRel X}
  : weakMonotone id.
Proof.
  unshelve esplit.
  intros x y p.
  exact p.
Qed.

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
       {X Y Z : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
       `{HZ : CompatRel Z}
       (f : X -> Y)
       (g : Y -> Z)
       `{@strictMonotone _ _ HX HY f}
       `{@strictMonotone _ _ HY HZ g}
  : strictMonotone (g o f).
Proof.
  unshelve esplit.
  intros x y p ; cbn.
  do 2 apply map_gt.
  assumption.
Qed.

Global Instance comp_weakMonotone
       {X Y Z : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
       `{HZ : CompatRel Z}
       (f : X -> Y)
       (g : Y -> Z)
       `{@weakMonotone _ _ HX HY f}
       `{@weakMonotone _ _ HY HZ g}
  : weakMonotone (g o f).
Proof.
  unshelve esplit.
  intros x y p ; cbn.
  do 2 apply map_ge.
  assumption.
Qed.

Global Instance fst_strictMonotone
       {X Y : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
  : strictMonotone (@fst X Y).
Proof.
  unshelve esplit.
  intros x y p.
  apply p.
Qed.

Global Instance fst_weakMonotone
       {X Y : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
  : weakMonotone (@fst X Y).
Proof.
  unshelve esplit.
  intros x y p.
  apply p.
Qed.

Global Instance snd_strictMonotone
       {X Y : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
  : strictMonotone (@snd X Y).
Proof.
  unshelve esplit.
  intros x y p.
  apply p.
Qed.

Global Instance snd_weakMonotone
       {X Y : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
  : weakMonotone (@snd X Y).
Proof.
  unshelve esplit.
  intros x y p.
  apply p.
Qed.

Global Instance pair_weakMonotone
       {X Y Z : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
       `{HZ : CompatRel Z}
       (f : X -> Y)
       (g : X -> Z)
       `{@weakMonotone _ _ HX HY f}
       `{@weakMonotone _ _ HX HZ g}
  : weakMonotone (fun x => (f x , g x)).
Proof.
  unshelve esplit.
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
       {X Y Z : Type}
       `{HX : CompatRel X}
       `{HY : CompatRel Y}
       `{HZ : CompatRel Z}
       (f : X -> Y)
       (g : X -> Z)
       `{@strictMonotone _ _ HX HY f}
       `{@strictMonotone _ _ HX HZ g}
  : strictMonotone (fun x => (f x , g x)).
Proof.
  unshelve esplit.
  intros x y p.
  split.
  - simpl.
    apply map_gt.
    assumption.
  - simpl.
    apply map_gt.
    assumption.
Qed.
