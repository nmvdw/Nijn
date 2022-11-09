Require Import Prelude.Funext.
Require Import Prelude.Basics.
Require Import Prelude.Props.
Require Import Prelude.WellfoundedRelation.
Require Import Prelude.Orders.CompatibleRelation.
Require Import Prelude.Orders.MonotonicMaps.
Require Import Lia.
Require Import Coq.Program.Equality.

Declare Scope compat.
Open Scope compat.

(** * Exmaples of compatible relations *)

(** The unit type *)
Definition unit_CompatRel : CompatRel
  := {| carrier := unit ;
        gt _ _ := False ;
        ge _ _ := True |}.

(** This relation is well-founded *)
Proposition unit_Wf : Wf (fun (x y : unit_CompatRel) => x > y).
Proof.
  intro z.
  apply acc.
  cbn.
  contradiction.
Qed.

Global Instance unit_isCompatRel : isCompatRel unit_CompatRel.
Proof.
  unshelve esplit ; cbn ; auto ; try (apply _).
Qed.

Definition unit_strict_minimal_element
  : strict_minimal_element unit_CompatRel.
Proof.
  simple refine (make_strict_min_el _ _ _).
  - exact tt.
  - intros y Hx.
    induction y.
    contradiction.
Defined.

Definition unit_minimal_element
  : minimal_element unit_CompatRel
  := is_minimal_to_strict_minimal unit_strict_minimal_element.

(** Compatible relations are well-founded *)
Definition prod_CompatRel
           (X Y : CompatRel)
  : CompatRel
  := {| carrier := X * Y ;
        gt x y := (fst x > fst y) /\ (snd x > snd y) ;
        ge x y := (fst x >= fst y) /\ (snd x >= snd y) |}.

Notation "X * Y" := (prod_CompatRel X Y) : compat.

(** The product of well-founded orders is again well-founded *)
Definition isWf_pair
           (X Y : CompatRel)
           {x : X} {y : Y}
           (Hx : isWf (@gt X) x)
           (Hy : isWf (@gt Y) y)
  : isWf (@gt _) ((x , y) : prod_CompatRel X Y).
Proof.
  revert Hy.
  revert y.
  induction Hx as [x Hx IHx].
  intros y HY.
  induction HY as [y Hy].
  apply acc.
  intros [z1 z2] [Hz1 Hz2] ; simpl in *.
  apply IHx.
  - assumption.
  - apply Hy.
    assumption.
Qed.

Proposition Wf_prod
            (X Y : CompatRel)
            (HX : Wf (@gt X))
            (HY : Wf (@gt Y))
  : Wf (@gt (X * Y)).
Proof.
  intros x.
  destruct x as [x y].
  apply isWf_pair.
  - apply HX.
  - apply HY.
Qed.

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

Definition prod_minimal_element
           {X Y : CompatRel}
           (x : minimal_element X)
           (y : minimal_element Y)
  : minimal_element (X * Y).
Proof.
  simple refine (make_min_el _ _ _).
  - exact (min_el _ x , min_el _ y).
  - intro z.
    split ; cbn.
    + apply is_minimal.
    + apply is_minimal.
Defined.

(**
 
 *)
Definition tuple_CompatRel
          (X : CompatRel)
          (Y : QuasiRel)
  : CompatRel
  := {| carrier := X * Y ;
        gt x y := fst x > fst y /\ (snd x >= snd y)%qr ;
        ge x y := fst x >= fst y /\ (snd x >= snd y)%qr |}.

Global Instance tuple_isCompatRel
              (X : CompatRel)
              `{isCompatRel X}
              (Y : QuasiRel)
              `{isQuasiRel Y}
  : isCompatRel (tuple_CompatRel X Y).
Proof.
  unshelve esplit ; cbn ; try (intros ; apply _).
  - intros x y z [ p1 p2 ] [ q1 q2 ].
    split.
    + exact (gt_trans p1 q1).
    + exact (ge_qr_trans p2 q2).
  - intros x y z [ p1 p2 ] [ q1 q2 ].
    split.
    + exact (ge_trans p1 q1).
    + exact (ge_qr_trans p2 q2).
  - intros x.
    split.
    + apply ge_refl.
    + apply ge_qr_refl.
  - intros x y [ p1 p2 ].
    split.
    + exact (compat p1).
    + exact p2.
  - intros x y z [ p1 p2 ] [ q1 q2 ].
    split.
    + exact (ge_gt p1 q1).
    + exact (ge_qr_trans p2 q2).
  - intros x y z [ p1 p2 ] [ q1 q2 ].
    split.
    + exact (gt_ge p1 q1).
    + exact (ge_qr_trans p2 q2).
Qed.

Definition isWf_pair_tuple
           (X : CompatRel)
           (Y : QuasiRel)
           {x : X} {y : Y}
           (Hx : isWf (@gt X) x)
  : isWf (@gt _) ((x , y) : tuple_CompatRel X Y).
Proof.
  revert y.
  induction Hx as [x Hx IHx].
  intros y.
  apply acc.
  intros [z1 z2] [Hz1 Hz2] ; simpl in *.
  apply IHx.
  assumption.
Qed.

Proposition Wf_tuple
           (X : CompatRel)
           (Y : QuasiRel)
           (HX : Wf (@gt X))
  : Wf (@gt (tuple_CompatRel X Y)).
Proof.
  intros x.
  destruct x as [x y].
  apply isWf_pair_tuple.
  apply HX.
Qed.
          
(** Dependent product of well-founded relations *)
Definition depprod_CompatRel
           {X : Type}
           (Y : X -> CompatRel)
  : CompatRel
  := {| carrier := (forall (x : X), Y x) ;
        gt f g := forall (x : X), f x > g x ;
        ge f g := forall (x : X), f x >= g x |}.

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

Definition depprod_minimal_element
           {X : Type}
           (Y : X -> CompatRel)
           (y : forall (x : X), minimal_element (Y x))
  : minimal_element (∏ Y).
Proof.
  simple refine (make_min_el _ _ _).
  - exact (fun x => y x).
  - intros z x.
    apply is_minimal.
Defined.

(** The power of well-founded relations *)
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

Definition power_minimal_element
           (X : CompatRel)
           (n : nat)
           (x : minimal_element X)
  : minimal_element (X ^ n).
Proof.
  induction n as [ | n IHn ].
  - apply unit_minimal_element.
  - apply prod_minimal_element.
    + exact x.
    + exact IHn.
Defined.

(** The natural numbers have the structure of well-founded relation *)
Definition nat_CompatRel
  : CompatRel
  := {| carrier := nat ;
        gt n m := n > m ;
        ge n m := n >= m |}%nat.

(** The strict order is well-founded *)
Proposition nat_Wf : Wf (@gt nat_CompatRel).
Proof.
  intro n.
  induction n as [ | n IHn ].
  - apply acc.
    intros ; simpl in *.
    lia.
  - inversion IHn.
    apply acc.
    intros y Hy.
    assert (n > y \/ n = y)%nat as X by (simpl in * ; lia).
    destruct X.
    + apply H.
      assumption.
    + subst.
      exact IHn.
Qed.

Global Instance nat_isCompatRel
  : isCompatRel nat_CompatRel.
Proof.
  unshelve esplit ; cbn ; intros ; try lia ; try (apply _).
Qed.

Definition nat_strict_minimal_element
  : strict_minimal_element nat_CompatRel.
Proof.
  simple refine (make_strict_min_el _ _ _).
  - exact 0.
  - intros n Hn.
    cbn.
    lia.
Defined.

Definition nat_minimal_element
  : minimal_element nat_CompatRel
  := is_minimal_to_strict_minimal nat_strict_minimal_element.

(**
 Function space of weakly monotonic maps
 *)
Definition fun_CompatRel
           (X Y : CompatRel)
  : CompatRel
  := {| carrier := weakMonotoneMap X Y ;
        gt f g := forall (x : X), f x > g x ;
        ge f g := forall (x : X), f x >= g x  |}.

Notation "X →wm Y" := (fun_CompatRel X Y) (at level 99).

Global Instance fun_isCompatRel
       (X Y : CompatRel)
       `{isCompatRel Y}
  : isCompatRel (X →wm Y).
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

(** The function space is well-founded if we can find an element of the domain *)
Proposition fun_Wf
            (X Y : CompatRel)
            (x : X)
            (HY : Wf (fun (x y : Y) => x > y))
  : Wf (fun (f g : fun_CompatRel X Y) => f > g).
Proof.
  simple refine (fiber_Wf HY _ _).
  - exact (fun f => f x).
  - intros f g p ; simpl.
    apply p.
Qed.

(**
 Function space of strongly monotonic maps
 *)
Definition strong_fun_CompatRel
           (X Y : CompatRel)
  : CompatRel
  := {| carrier := strongMonotoneMap X Y ;
        gt f g := forall (x : X), f x > g x ;
        ge f g := forall (x : X), f x >= g x  |}.

Notation "X ==> Y" := (strong_fun_CompatRel X Y) (at level 99).

Global Instance strong_fun_isCompatRel
       (X Y : CompatRel)
       `{isCompatRel Y}
  : isCompatRel (X ==> Y).
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

(** The function space is well-founded if we can find an element of the domain *)
Proposition strong_fun_Wf
            (X Y : CompatRel)
            (x : X)
            (HY : Wf (fun (x y : Y) => x > y))
  : Wf (fun (f g : strong_fun_CompatRel X Y) => f > g).
Proof.
  simple refine (fiber_Wf HY _ _).
  - exact (fun f => f x).
  - intros f g p ; simpl.
    apply p.
Qed.

(** * Examples of weakly monotone maps *)

(** The constant functions *)
Global Instance const_weakMonotone
       (X Y : CompatRel)
       `{isCompatRel Y}
       (y : Y)
  : weakMonotone (fun (_ : X) => y).
Proof.
  intros x1 x2 p.
  apply ge_refl.
Qed.

Definition const_wm
           {X Y : CompatRel}
           `{isCompatRel Y}
           (y : Y)
  : X →wm Y
  := make_monotone (fun (_ : X) => y) _.

Definition min_el_fun_space
           {X : CompatRel}
           {Y : CompatRel}
           `{isCompatRel Y}
           (m : minimal_element Y)
  : minimal_element (X →wm Y).
Proof.
  simple refine (make_min_el _ _ _).
  - exact (const_wm m).
  - intros f x.
    apply m.
Defined.

(** The identity function *)
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

Definition id_wm
           {X : CompatRel}
  : X →wm X
  := make_monotone id _.

Definition id_strong_monotone
           {X : CompatRel}
  : X ==> X
  := make_strong_monotone id _ _.

(** The composition *)
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

Definition comp_wm
           {X Y Z : CompatRel}
           (f : X →wm Y)
           (g : Y →wm Z)
  : X →wm Z
  := make_monotone (g o f) _.

Notation "g ∘wm f" := (comp_wm f g) (at level 40).

Definition comp_strong_monotone
           {X Y Z : CompatRel}
           (f : X ==> Y)
           (g : Y ==> Z)
  : X ==> Z
  := make_strong_monotone (g o f) _ _.

(** The first projection *)
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

Definition fst_wm
           {X Y : CompatRel}
  : (X * Y) →wm X
  := make_monotone _ _.

Definition fst_strong_monotone
           {X Y : CompatRel}
  : (X * Y) ==> X
  := make_strong_monotone _ _ _.

(** The second projection *)
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

Definition snd_wm
           {X Y : CompatRel}
  : (X * Y) →wm Y
  := make_monotone _ _.

Definition snd_strong_monotone
           {X Y : CompatRel}
  : (X * Y) ==> Y
  := make_strong_monotone _ _ _.

(** The pairing of weakly monotone maps *)
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

Definition pair_wm
           {X Y Z : CompatRel}
           (f : X →wm Y)
           (g : X →wm Z)
  : X →wm (Y * Z)
  := @make_monotone X (Y * Z) (fun x => (f x , g x)) _.

Notation "⟨ f , g ⟩" := (pair_wm f g).

Definition pair_strong_monotone
           {X Y Z : CompatRel}
           (f : X ==> Y)
           (g : X ==> Z)
  : X ==> (Y * Z)
  := @make_strong_monotone X (Y * Z) (fun x => (f x , g x)) _ _.

(** Lambda abstraction *)
Global Instance lambda_abs_on_X_monotone
       {X Y Z : CompatRel}
       `{isCompatRel X}
       (f : Y * X →wm Z)
       (x : X)
  : weakMonotone (fun y => f (y , x)).
Proof.
  intros z1 z2 p.
  apply map_ge.
  split.
  - exact p.
  - apply ge_refl.
Qed.

Definition lambda_abs_on_X
           {X Y Z : CompatRel}
           `{isCompatRel X}
           (f : Y * X →wm Z)
           (x : X)
  : Y →wm Z
  := make_monotone (fun y => f (y , x)) _.

Global Instance lambda_abs_mon
       {X Y Z : CompatRel}
       `{isCompatRel X}
       `{isCompatRel Y}
       (f : X * Y →wm Z)
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
            (f : Y * X →wm Z)
  : X →wm (Y →wm Z)
  := make_monotone (fun x : X => lambda_abs_on_X f x) _.

Notation "'λwm' f" := (lambda_abs f) (at level 10).

Global Instance plus_isWeakMonotone
                {A : CompatRel}
                (f g : A -> nat_CompatRel)
                `{Hf : weakMonotone _ _ f}
                `{Hg : weakMonotone _ _ g}
  : weakMonotone (fun a => (f a + g a : nat_CompatRel)).
Proof.
  intros a1 a2 p.
  pose (Hf _ _ p).
  pose (Hg _ _ p).
  cbn in *.
  nia.
Qed.

Global Instance plus_isStrictMonotone
                {A : CompatRel}
                (f g : A -> nat_CompatRel)
                `{Hf : strictMonotone _ _ f}
                `{Hg : strictMonotone _ _ g}
  : strictMonotone (fun a => (f a + g a : nat_CompatRel)).
Proof.
  intros a1 a2 p.
  pose (Hf a1 a2 p).
  pose (Hg a1 a2 p).
  cbn in *.
  nia.
Qed.

Definition plus_fun_wm
           {A : CompatRel}
           (f g : A →wm nat_CompatRel)
  : A →wm nat_CompatRel
  := make_monotone (fun a => (f a + g a : nat_CompatRel)) _.

Definition plus_strong_monotone
           {A : CompatRel}
           (f g : A ==> nat_CompatRel)
  : A ==> nat_CompatRel
  := make_strong_monotone (fun a => (f a + g a : nat_CompatRel)) _ _.

Global Instance mult_isWeakMonotone
                {A : CompatRel}
                (f g : weakMonotoneMap A nat_CompatRel)
  : weakMonotone (fun a => (f a * g a : nat_CompatRel)%nat).
Proof.
  intros a1 a2 p.
  pose (is_weak_monotone _ _ f _ _ p).
  pose (is_weak_monotone _ _ g _ _ p).
  cbn in *.
  nia.
Qed.

Definition mult_fun_wm
           {A : CompatRel}
           (f g : weakMonotoneMap A nat_CompatRel)
  : weakMonotoneMap A nat_CompatRel
  := make_monotone (fun a => (f a * g a : nat_CompatRel)%nat) _.

Global Instance app_isWeakMonotone
                {A B C : CompatRel}
                `{isCompatRel C}
                (f : A →wm (B →wm C))
                (x : A →wm B)
  : weakMonotone (fun a : A => f a (x a)).
Proof.
  intros a1 a2 p.
  refine (ge_trans
            (is_weak_monotone _ _ f _ _ p (x a1))
            _).
  exact (is_weak_monotone _ _ (f a2) _ _ (is_weak_monotone _ _ x _ _ p)).
Qed.
  
Definition app_wm
           {A B C : CompatRel}
           `{isCompatRel C}
           (f : A →wm (B →wm C))
           (x : A →wm B)
  : A →wm C
  := make_monotone (fun a => f a (x a)) _.

Notation "f '·wm' x" := (app_wm f x) (at level 20, left associativity).

Global Instance strong_app_isWeakMonotone
                {A B C : CompatRel}
                `{isCompatRel C}
                (f : A ==> (B ==> C))
                (x : A ==> B)
  : weakMonotone (fun a : A => f a (x a)).
Proof.
  intros a1 a2 p.
  refine (ge_trans
            (strong_is_weak _ _ f _ _ p (x a1))
            _).
  exact (strong_is_weak _ _ (f a2) _ _ (strong_is_weak _ _ x _ _ p)).
Qed.

Global Instance strong_app_isStrictMonotone
                {A B C : CompatRel}
                `{isCompatRel C}
                (f : A ==> (B ==> C))
                (x : A ==> B)
  : strictMonotone (fun a : A => f a (x a)).
Proof.
  intros a1 a2 p.
  refine (gt_trans
            (strong_is_strict _ _ f _ _ p (x a1))
            _).
  exact (strong_is_strict _ _ (f a2) _ _ (strong_is_strict _ _ x _ _ p)).
Qed.

Definition app_strong_monotone
           {A B C : CompatRel}
           `{isCompatRel C}
           (f : A ==> (B ==> C))
           (x : A ==> B)
  : A ==> C
  := make_strong_monotone (fun a => f a (x a)) _ _.

(** We also need the following monotone maps *)
Definition plus_wm
  : nat_CompatRel * nat_CompatRel →wm nat_CompatRel
  := @make_monotone
       (nat_CompatRel * nat_CompatRel)
       nat_CompatRel
       (fun x => fst x + snd x)
       _.

Global Instance apply_el_is_weak_monotone
                {A₁ A₂ : CompatRel}
                (x : A₁)
  : @weakMonotone (A₁ →wm A₂) A₂ (fun f => f x).
Proof.
  intros h₁ h₂ p.
  apply p.
Qed.
  
Definition apply_el_wm
           {A₁ A₂ : CompatRel}
           (x : A₁)
  : (A₁ →wm A₂) →wm A₂
  := @make_monotone
       (A₁ →wm A₂)
       A₂
       (fun f => f x)
       _.
