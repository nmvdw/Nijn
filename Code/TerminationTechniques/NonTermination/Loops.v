Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.
Require Import Nijn.Syntax.StrongNormalization.SN.
Require Import Nijn.Syntax.Signature.SubTerm.
Require Import Nijn.Syntax.Signature.RewriteLemmas.
Require Import Nijn.Syntax.Signature.SubstitutionLemmas.

Import AFSNotation.

Section Loops.
  Context {B F : Type}
          (X : afs B F).

  Record loop : Type :=
    {
      loop_con : con B ;
      loop_ty : ty B ;
      loop_tm : tm X loop_con loop_ty ;
      loop_loop : loop_tm ∼> loop_tm
    }.

  Definition loop_to_infinite_chain
             (l : loop)
    : infinite_chain (fun t1 t2 : tm X (loop_con l) (loop_ty l) => t1 ∼> t2)
    := {| seq := fun n => loop_tm l ; decr n := loop_loop l |}.

  Theorem loop_to_notSN
          (l : loop)
    : ~(isSN X).
  Proof.
    intro H.
    apply (no_infinite_chain _ (H (loop_con l) (loop_ty l))).
    exact (loop_to_infinite_chain l).
  Qed.
End Loops.

Definition make_loop
           {B F : Type}
           (X : afs B F)
           (C : con B)
           {A : ty B}
           (t : tm X C A)
           (r : t ∼> t)
  : loop X
  := {| loop_con := C ;
        loop_ty := A ;
        loop_tm := t ;
        loop_loop := r |}.

Section IncreasingLoops.
  Context {B F : Type}
          (X : afs B F).

  Record inc_loop : Type :=
    {
      inc_loop_con : con B ;
      inc_loop_ty : ty B ;
      inc_loop_s : tm X inc_loop_con inc_loop_ty ;
      inc_loop_t : tm X inc_loop_con inc_loop_ty ;
      inc_loop_rew : inc_loop_s ∼> inc_loop_t ;
      inc_loop_subTm : inc_loop_s ≼ inc_loop_t 
    }.

  Record loop_point (l : inc_loop) :=
    {
      point_tm : tm X (inc_loop_con l) (inc_loop_ty l) ;
      point_subTm : inc_loop_s l ≼ point_tm
    }.

  Definition inc_loop_infinite_seq
             (l : inc_loop)
             (n : nat)
    : loop_point l.
  Proof.
    induction n as [ | n IHn ].
    - refine {| point_tm := inc_loop_t l |}.
      apply inc_loop_subTm.
    - refine {| point_tm := sub_subTerm (inc_loop_t l) (point_subTm _ IHn) |}.
      refine (subTm_trans _ (subTerm_of_sub_subTerm _ _)).
      exact (inc_loop_subTm l).
  Defined.

  Definition inc_loop_infinite_chain
             (l : inc_loop)
    : infinite_chain
        (fun (t1 t2 : tm X (inc_loop_con l) (inc_loop_ty l)) => t1 ∼> t2).
  Proof.
    refine {| seq n := point_tm _ (inc_loop_infinite_seq l n) |}.
    intro n.
    simpl.
    destruct n as [ | n ].
    - exact (rew_subTerm X (inc_loop_rew l) (inc_loop_subTm l)).
    - exact (rew_subTerm X (inc_loop_rew l) _).
  Defined.
      
  Theorem inc_loop_to_notSN
          (l : inc_loop)
    : ~(isSN X).
  Proof.
    intro H.
    apply (no_infinite_chain _ (H (inc_loop_con l) (inc_loop_ty l))).
    exact (inc_loop_infinite_chain l).
  Qed.
End IncreasingLoops.
