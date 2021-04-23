(** * Well-founded types *)

(** To formulate well-foundedness constructively, we make use of inductive subsets. *)
Inductive isWf {X : Type} (R : X -> X -> Type) (x : X) : Prop :=
| acc : (forall (y : X), R x y -> isWf R y) -> isWf R x.

Definition Wf {X : Type} (R : X -> X -> Type)
  := forall (x : X), isWf R x.

(** Well-founded types are closed under inverse images *)
Lemma fiber_is_Wf_help
      {X Y : Type}
      {RX : X -> X -> Type}
      {RY : Y -> Y -> Type}
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
            {RX : X -> X -> Type}
            {RY : Y -> Y -> Type}
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

(** If a type is well-founded, then there are no infinite decreasing chains in it *)

Record infinite_chain {X : Type} (R : X -> X -> Type) :=
  {
    seq :> nat -> X ;
    decr : forall (n : nat), R (seq n) (seq (S n))
  }.

Arguments decr {_} {_} _ _.

Definition shift
           {X : Type}
           {R : X -> X -> Type}
           (f : infinite_chain R)
  : infinite_chain R
  := {| seq n := f (S n) ;
        decr n := decr f (S n) |}.

Definition no_infinite_chain_help
           {X : Type}
           (R : X -> X -> Type)
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
           (R : X -> X -> Type)
           (HX : Wf R)
  : infinite_chain R -> False.
Proof.
  intro f.
  exact (no_infinite_chain_help R HX (f 0) f eq_refl).
Qed.
