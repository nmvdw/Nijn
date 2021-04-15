Inductive isWf {X : Type} (R : X -> X -> Prop) (x : X) : Prop :=
| acc : (forall (y : X), R x y -> isWf R y) -> isWf R x.

Definition Wf {X : Type} (R : X -> X -> Prop)
  := forall (x : X), isWf R x.

Definition lexico
           {X Y : Type}
           (RX : X -> X -> Prop)
           (RY : Y -> Y -> Prop)
  : X * Y -> X * Y -> Prop
  := fun x y => (RX (fst x) (fst y)) \/ (fst x = fst y /\ RY (snd x) (snd y)).

Proposition lexico_Wf
            {X Y : Type}
            (RX : X -> X -> Prop)
            (RY : Y -> Y -> Prop)
            (HX : Wf RX)
            (HY : Wf RY)
  : Wf (lexico RX RY).
Proof.
  intros [x y].
  pose (HX x) as Hx.
  revert y.
  induction Hx as [x Hx IHx].
  intros y.
  pose (HY y) as Hy.
  induction Hy as [y Hy IHy].
  apply acc.
  intros [z1 z2] [Hz | [Hz1 Hz2]].
  - simpl in *.
    apply IHx.
    assumption.
  - simpl in *.
    subst.
    apply IHy.
    apply Hz2.
Qed.

Lemma fiber_is_Wf_help
      {X Y : Type}
      {RX : X -> X -> Prop}
      {RY : Y -> Y -> Prop}
      {f : X -> Y}
      (Hf : forall (x1 x2 : X), RX x1 x2 -> RY (f x1) (f x2))
      (y : Y)
  : isWf RY y -> forall (x : X), y = f x -> isWf RX x.
Proof.
  intros H.
  induction H as [fx Hfx IHfx].
  intros x p.
  subst.
  apply acc.
  intros z Hz.
  apply (IHfx (f z)).
  - apply Hf.
    exact Hz.
  - reflexivity.
Qed.

Proposition fiber_is_Wf
            {X Y : Type}
            {RX : X -> X -> Prop}
            {RY : Y -> Y -> Prop}
            (HY : Wf RY)
            (f : X -> Y)
            (Hf : forall (x1 x2 : X), RX x1 x2 -> RY (f x1) (f x2))
  : Wf RX.
Proof.
  intro x.
  pose (fx := f x).
  pose (Hfx := HY fx).
  exact (fiber_is_Wf_help Hf fx Hfx x eq_refl).
Qed.

Record infinite_chain {X : Type} (R : X -> X -> Prop) :=
  {
    seq :> nat -> X ;
    decr : forall (n : nat), R (seq n) (seq (S n))
  }.

Arguments decr {_} {_} _ _.

Definition shift
           {X : Type}
           {R : X -> X -> Prop}
           (f : infinite_chain R)
  : infinite_chain R
  := {| seq n := f (S n) ;
        decr n := decr f (S n) |}.

Definition no_infinite_chain_help
           {X : Type}
           (R : X -> X -> Prop)
           (HX : Wf R)
  : forall (x : X)
           (f : infinite_chain R)
           (p : f 0 = x),
    False.
Proof.
  intro x.
  pose (Hx :=  HX x).
  induction Hx as [x Hx IHx].
  intros f p.
  assert (R x (f 1)) as Hxf.
  {
    subst.
    apply f.
  }
  exact (IHx (f 1) Hxf (shift f) eq_refl).
Qed.

Definition no_infinite_chain
           {X : Type}
           (R : X -> X -> Prop)
           (HX : Wf R)
  : infinite_chain R -> False.
Proof.
  intro f.
  exact (no_infinite_chain_help R HX (f 0) f eq_refl).
Qed.
