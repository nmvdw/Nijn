(** * Well-founded types *)

(** To formulate well-foundedness constructively, we make use of inductive subsets. *)
Inductive isWf {X : Type} (R : X -> X -> Type) (x : X) : Prop :=
| acc : (forall (y : X), R x y -> isWf R y) -> isWf R x.

Definition Wf {X : Type} (R : X -> X -> Type)
  := forall (x : X), isWf R x.

(** Well-founded types are closed under inverse images *)
Lemma fiber_isWf
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

Proposition fiber_Wf
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
  exact (fiber_isWf Hf fx Hfx x eq_refl).
Qed.

(** * Normal forms of a relation *)
Definition nf
           {A : Type}
           (R : A -> A -> Type)
           (a : A)
  : Prop
  := forall (b : A), R a b -> False.

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

Theorem no_infinite_chain_help
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

Theorem no_infinite_chain
        {X : Type}
        (R : X -> X -> Type)
        (HX : Wf R)
  : infinite_chain R -> False.
Proof.
  intro f.
  exact (no_infinite_chain_help R HX (f 0) f eq_refl).
Qed.

(** The converse holds if we assume double negation elimination *)
Section Classical.
  Context {X : Type}
          (R : X -> X -> Type)
          (DN : forall (P : Type), ((P -> False) -> False) -> P).
             
  Definition next_one_pair
             (x : X)
             (Hx : isWf R x -> False)
    : { y : X & R x y * (isWf R y -> False) }%type.
  Proof.
    apply DN.
    intro H.
    assert (forall (z : X), (R x z -> False) \/ isWf R z) as H'.
    {
      intros z.
      assert ((R x z * (isWf R z -> False)) -> False) as C.
      {
        intro Hz.
        apply H.
        unshelve esplit.
        - exact z.
        - exact Hz.
      }
      apply DN.
      intro H'.
      apply C.
      split.
      - apply DN.
        intro.
        apply H'.
        left.
        assumption.
      - apply DN.
        intro.
        apply H'.
        right.
        apply DN.
        assumption.
    }
    apply Hx.
    apply acc.
    intros y Rxy.
    destruct (H' y).
    - contradiction.
    - assumption.
  Qed.
  
  Definition next_one
             (x : X)
             (Hx : isWf R x -> False)
    : X
    := projT1 (next_one_pair x Hx).

  Definition next_one_rel
             (x : X)
             (Hx : isWf R x -> False)
    : R x (next_one x Hx)
    := fst (projT2 (next_one_pair x Hx)).

  Definition next_one_not_Wf
             (x : X)
             (Hx : isWf R x -> False)
    : isWf R (next_one x Hx) -> False
    := snd (projT2 (next_one_pair x Hx)).
  
  Definition infinite_seq_from_not_isWf_pair
             (x : X)
             (Hx : isWf R x -> False)
             (n : nat)
    : { y : X & isWf R y -> False }.
  Proof.
    induction n as [ | n IHn ].
    - unshelve esplit.
      + exact x.
      + exact Hx.
    - unshelve esplit.
      + exact (next_one (projT1 IHn) (projT2 IHn)).
      + exact (next_one_not_Wf (projT1 IHn) (projT2 IHn)).
  Defined.

  Definition infinite_seq_from_not_isWf
             (x : X)
             (Hx : isWf R x -> False)
             (n : nat)
    : X
    := projT1 (infinite_seq_from_not_isWf_pair x Hx n).

  Definition infinite_seq_from_not_isWf_not_Wf
             (x : X)
             (Hx : isWf R x -> False)
             (n : nat)
    := projT2 (infinite_seq_from_not_isWf_pair x Hx n).

  Proposition infinite_seq_from_decr
              (x : X)
              (Hx : isWf R x -> False)
              (n : nat)
    : R (infinite_seq_from_not_isWf x Hx n) (infinite_seq_from_not_isWf x Hx (S n)).
  Proof.
    apply next_one_rel. 
  Qed.

  Definition infinite_chain_from_not_isWf
             (x : X)
             (Hx : isWf R x -> False)
    : infinite_chain R
    := {|
          seq := infinite_seq_from_not_isWf x Hx ;
          decr := infinite_seq_from_decr x Hx
       |}.
  
  Theorem no_inifnite_chain_to_wf
          (H : infinite_chain R -> False)
    : Wf R.
  Proof.
    intro x.
    apply DN.
    intros H'.
    apply H.
    apply (infinite_chain_from_not_isWf x H').
  Qed.
End Classical.
