Require Import Prelude.Wellfounded.
Require Import Syntax.Signature.

Import AFSNotation.

Definition isSN
           {B F R : Type}
           (X : AFS B F R)
  : Prop
  := forall (C : Con B) (A : Ty B), Wf (@Rew _ _ _ X C A).

Definition Ty_isSN
           {B F R : Type}
           (X : AFS B F R)
           (A : Ty B)
  : Prop
  := forall (C : Con B), Wf (@Rew _ _ _ X C A).

Definition map_Tm
           {B F R : Type}
           {X : AFS B F R}
           {C : Con B}
           (A : Ty B)
           {A' : Ty B}
           (t : Tm X C A')
  : Tm X ((A' ⟶ A),, C) A
  := TmVar Vz · wkTm t (Drop _ (idWk C)).

Definition Rew_Wk
           {B F R : Type}
           {X : AFS B F R}
           {C1 C2 : Con B}
           {A : Ty B}
           {t1 t2 : Tm X C2 A}
           (w : Wk C1 C2)
           (p : Rew X t1 t2)
  : Rew X (wkTm t1 w) (wkTm t2 w).
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
    assert (compSub
              (wkToSub (Keep A1 w))
              (idSub C1 (Arity X) & subTm x (wkToSub w))
            =
            compSub
              (idSub C (Arity X) & x)
              (wkToSub w)) as H.
    {      
      admit.
    }
    unfold beta_sub.
    rewrite <- H.
    rewrite <- subTm_comp.
    apply Beta.
  - rewrite !wkTm_is_subTm.
    rewrite !subTm_comp.
    apply BaseRew.
Admitted.

Definition Rew_map_Tm
           {B F R : Type}
           {X : AFS B F R}
           {C : Con B}
           {A A' : Ty B}
           {t1 t2 : Tm X C A'}
           (p : Rew X t1 t2)
  : Rew X (map_Tm A t1) (map_Tm A t2).
Proof.
  unfold map_Tm.
  apply Rew_App_r.
  apply Rew_Wk.
  exact p.
Qed.

Theorem SN_if_TySN
        {B F R : Type}
        (X : AFS B F R)
        (A : Ty B)
        (H : Ty_isSN X A)
  : isSN X.
Proof.
  intros C A'.
  simple refine (fiber_is_Wf (H ((A' ⟶ A) ,, C)) _ _).
  - exact (map_Tm _).
  - intros t1 t2.
    exact Rew_map_Tm.
Qed.    
