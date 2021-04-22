Require Import Prelude.Wellfounded.
Require Import Syntax.Signature.
Require Import Syntax.Signature.SubstitutionLemmas.

Import AFSNotation.

(** * Strong normalization *)

(** An AFS is strongly normalizing if the rewriting relation is well-founded *)
Definition isSN
           {B F R : Type}
           (X : afs B F R)
  : Prop
  := forall (C : con B) (A : ty B), Wf (@rew _ _ _ X C A).

(** A type is said to be strongly normalizing if the rewrite relations of terms on that type is strongly normalizing *)
Definition Ty_isSN
           {B F R : Type}
           (X : afs B F R)
           (A : ty B)
  : Prop
  := forall (C : con B), Wf (@rew _ _ _ X C A).

(** We show that if one type is strongly normalizing, then all types are. Hence, it is sufficient to check for strong normalization in just one type. *)
Definition map_Tm
           {B F R : Type}
           {X : afs B F R}
           {C : con B}
           (A : ty B)
           {A' : ty B}
           (t : tm X C A')
  : tm X ((A' ⟶ A),, C) A
  := TmVar Vz · wkTm t (Drop _ (idWk C)).

Definition Rew_Wk
           {B F R : Type}
           {X : afs B F R}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm X C2 A}
           (w : wk C1 C2)
           (p : rew X t1 t2)
  : rew X (wkTm t1 w) (wkTm t2 w).
Proof.
  revert w.
  revert C1.
  induction p ; intros C1 w ; simpl.
  - exact (Trans (IHp1 C1 w) (IHp2 C1 w)).
  - exact (Rew_App_l _ (IHp C1 w)).
  - exact (Rew_App_r _ (IHp C1 w)).
  - exact (Rew_Lam (IHp _ (Keep A1 w))).
  - simpl.
    rewrite !wkTm_is_subTm.
    rewrite subTm_comp.
    unfold beta_sub.
    rewrite <- beta_sub_help.
    rewrite <- subTm_comp.
    apply Beta.
  - rewrite !wkTm_is_subTm.
    rewrite !subTm_comp.
    apply BaseRew.
Qed.

Definition Rew_map_Tm
           {B F R : Type}
           {X : afs B F R}
           {C : con B}
           {A A' : ty B}
           {t1 t2 : tm X C A'}
           (p : rew X t1 t2)
  : rew X (map_Tm A t1) (map_Tm A t2).
Proof.
  unfold map_Tm.
  apply Rew_App_r.
  apply Rew_Wk.
  exact p.
Qed.

Theorem SN_if_TySN
        {B F R : Type}
        (X : afs B F R)
        (A : ty B)
        (H : Ty_isSN X A)
  : isSN X.
Proof.
  intros C A'.
  simple refine (fiber_is_Wf (H ((A' ⟶ A) ,, C)) _ _).
  - exact (map_Tm _).
  - intros t1 t2.
    exact Rew_map_Tm.
Qed.    
