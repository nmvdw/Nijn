Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.
Require Import Nijn.Syntax.Signature.SubstitutionLemmas.
Require Import Coq.Program.Equality.

(** * Lemmas on the rewriting relation *)

(** ** Beta reduction is reflected under weakening *)
Lemma is_BaseTm_wkTm
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C1 C2 : con B}
      (w : wk C1 C2)
      {A : ty B}
      {t : tm ar C2 A}
      (Ht : is_BaseTm t)
  : is_BaseTm (wkTm t w).
Proof.
  induction t ; try contradiction.
  apply I.
Qed.

Definition wWeakened
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           (w : wk C1 C2)
           {A : ty B}
           (t : tm ar C1 A)
  : Type
  := { t' : tm ar C2 A | wkTm t' w = t  }.

Definition term_of
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {w : wk C1 C2}
           {A : ty B}
           {t : tm ar C1 A}
           (p : wWeakened w t)
  : tm ar C2 A.
Proof.
  destruct p as [x e].
  exact x.
Defined.

Definition term_of_eq
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {w : wk C1 C2}
           {A : ty B}
           {t : tm ar C1 A}
           (p : wWeakened w t)
  : wkTm (term_of p) w = t.
Proof.
  destruct p as [x e].
  exact e.
Defined.

Definition wkTm_red_lam_help
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           (w : wk C1 C2)
           {A1 A2 A' : ty B}
           (t : tm ar C2 A')
           (f : tm ar (A1 ,, C1) A2)
           (p : A' = (A1 ⟶ A2))
           (q : wkTm (transport _ p t) w = λ f)
  : { t' : tm ar (A1 ,, C2) A2 | transport _ p t = λ t' }.
Proof.
  destruct t ; try (subst ; simpl in * ; discriminate).
  - enough (is_BaseTm (λ f)) by contradiction.
    rewrite <- q.
    apply is_BaseTm_wkTm.
    apply transport_BaseTm.
    apply I.
  - dependent destruction p ; simpl.
    exists t.
    reflexivity.
Qed.

Definition wkTm_red_lam
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           (w : wk C1 C2)
           {A1 A2 : ty B}
           (t : tm ar C2 (A1 ⟶ A2))
           (f : tm ar (A1 ,, C1) A2)
           (q : wkTm t w = λ f)
  : { t' : tm ar (A1 ,, C2) A2 | t = λ t' }.
Proof.
  exact (wkTm_red_lam_help w t f eq_refl q).
Qed.

Proposition wkTm_red_step
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            {w : wk C1 C2}
            {A : ty B}
            {t1 t2 : tm ar C1 A}
            (p : wWeakened w t1)
            (r : t1 ∼>β t2)
  : { q : wWeakened w t2 & term_of p ∼>β term_of q }.
Proof.
  revert p.
  revert w.
  revert C2.
  induction r ; intros C2 w p.
  - destruct p as [t' p].
    destruct t' ; simpl in * ; try discriminate.
    assert (p1 := App_eq_Ty p).
    assert (p2 := App_eq_fst p).
    assert (p3 := App_eq_snd p).
    dependent destruction p.
    simpl in *.
    specialize (IHr _ _ (exist _ t'1 p2)).
    destruct IHr as [q Hq].
    destruct q as [v q].
    unshelve eexists.
    + unshelve eexists.
      * refine (v · t'2).
      * simpl.
        subst.
        reflexivity.
    + simpl.
      apply App_l.
      assumption.
  - destruct p as [t' p].
    destruct t' ; simpl in * ; try discriminate.
    assert (p1 := App_eq_Ty p).
    assert (p2 := App_eq_fst p).
    assert (p3 := App_eq_snd p).
    dependent destruction p.
    simpl in *.
    specialize (IHr _ _ (exist _ t'2 p3)).
    destruct IHr as [q Hq].
    destruct q as [v q].
    unshelve eexists.
    + unshelve eexists.
      * refine (t'1 · v).
      * simpl.
        subst.
        reflexivity.
    + simpl.
      apply App_r.
      assumption.
  - destruct p as [t' p].
    destruct (wkTm_red_lam w t' f1 p) as [x e].
    subst.
    pose (q' := Lam_eq p).
    specialize (IHr _ (Keep A1 w) (exist _ _ q')).
    destruct IHr as [z Hz].
    destruct z as [z Hz'].
    unshelve eexists.
    + unshelve eexists.
      * refine (λ z).
      * simpl.
        rewrite  Hz'.
        reflexivity.
    + simpl.
      apply CLam.
      assumption.
  - induction r.
    simpl in *.
    destruct p as [t' p].
    destruct t' ; simpl in * ; try discriminate.
    assert (p1 := App_eq_Ty p).
    subst.
    assert (p2 := App_eq_fst p).
    assert (p3 := App_eq_snd p).
    rewrite (UIP (App_eq_Ty p) eq_refl) in p2.
    rewrite (UIP (App_eq_Ty p) eq_refl) in p3.
    simpl in *.
    destruct (wkTm_red_lam w t'1 f p2) as [x' e].
    subst.
    simpl in *.
    unshelve eexists.
    + unshelve eexists.
      * exact (x' [ beta_sub t'2 ]).
      * abstract
          (rewrite <- (Lam_eq p2) ;
           rewrite !wkTm_is_subTm ;
           rewrite !subTm_comp ;
           f_equal ;
           simpl ; cbn ;
           rewrite Sub_id_left ;
           f_equal ;
           unfold beta_sub ;
           simpl ;
           rewrite dropSub_is_compSubWk ;
           rewrite <- compSub_compWkSub ;
           simpl ; cbn; 
           rewrite compWkSub_id ; 
           rewrite Sub_id_right ; 
           reflexivity).
    + simpl.
      apply CStep.
      apply Beta.
Qed.

Proposition wkTm_red
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A : ty B}
            {t1 t2 : tm ar C1 A}
            (p : wWeakened w t1)
            (r : t1 ∼>β+ t2)
  : { q : wWeakened w t2 & term_of p ∼>β+ term_of q }.
Proof.
  induction r as [ ? ? r | ? ? ? r1 IHr1 r2 IHr2].
  - pose (wkTm_red_step p r) as H.
    destruct H as [q Hq].
    exists q.
    apply betaRed_step.
    exact Hq.
  - specialize (IHr1 p).
    destruct IHr1 as [q Hq].
    specialize (IHr2 q).
    destruct IHr2 as [q' Hq'].
    exists q'.
    exact (beta_Trans Hq Hq').
Qed.


(** ** Beta reduction *)
Definition betaRed_step_Wk
           {B F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm ar C2 A}
           (w : wk C1 C2)
           (p : t1 ∼>β t2)
  : wkTm t1 w ∼>β wkTm t2 w.
Proof.
  revert w.
  revert C1.
  induction p ; intros C1 w ; simpl.
  - exact (App_l _ (IHp _ w)).
  - exact (App_r _ (IHp _ w)).
  - exact (CLam (IHp _ (Keep A1 w))).
  - apply CStep.
    induction r.
    rewrite !wkTm_is_subTm.
    rewrite subTm_comp.
    unfold beta_sub.
    rewrite <- beta_sub_help.
    rewrite <- subTm_comp.
    apply Beta.
Qed.

Definition betaRed_Wk
           {B F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm ar C2 A}
           (w : wk C1 C2)
           (p : t1 ∼>β+ t2)
  : wkTm t1 w ∼>β+ wkTm t2 w.
Proof.
  revert w.
  revert C1.
  induction p ; intros C1 w ; simpl.
  - apply betaRed_step.
    apply betaRed_step_Wk.
    exact r.
  - exact (beta_Trans (IHp1 C1 w) (IHp2 C1 w)).
Qed.

(** Rewriting is closed under substitution *)
Definition betaRed_step_sub
           {B F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm ar C2 A}
           (s : sub ar C1 C2)
           (p : t1 ∼>β t2)
  : t1 [ s ] ∼>β t2 [ s ].
Proof.
  revert s.
  revert C1.
  induction p ; intros C1 s ; simpl.
  - exact (App_l _ (IHp _ s)).
  - exact (App_r _ (IHp _ s)).
  - exact (CLam (IHp _ (keepSub A1 s))).
  - apply CStep.
    induction r.
    simpl.
    pose (Beta (f [ keepSub A1 s ]) (x [ s ])) as p.
    unfold beta_sub in *.
    assert (f [ keepSub A1 s ] [ idSub C1 _ && x [ s ] ]
            =
            f [ idSub C _ && x ] [ s ])
      as H.
    {
      rewrite subTm_comp.
      unfold keepSub.
      rewrite dropSub_is_compSubWk.
      simpl ; cbn.
      rewrite <- compSub_compWkSub.
      simpl ; cbn.
      rewrite compWkSub_id.
      rewrite Sub_id_right.
      rewrite subTm_comp.
      simpl ; cbn.
      rewrite Sub_id_left.
      reflexivity.
    }
    rewrite H in p.
    exact p.
Qed.

Definition betaRed_sub
           {B F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm ar C2 A}
           (s : sub ar C1 C2)
           (p : t1 ∼>β+ t2)
  : t1 [ s ] ∼>β+ t2 [ s ].
Proof.
  revert s.
  revert C1.
  induction p ; intros C1 s ; simpl.
  - apply betaRed_step.
    apply betaRed_step_sub.
    exact r.
  - exact (beta_Trans (IHp1 C1 s) (IHp2 C1 s)).
Qed.

(** ** Rewriting in an AFS *)

Import AFSNotation.

(** Rewriting is closed under weakening *)
Definition Rew_Wk
           {B F : Type}
           {X : afs B F}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm X C2 A}
           (w : wk C1 C2)
           (p : t1 ∼> t2)
  : wkTm t1 w ∼> wkTm t2 w.
Proof.
  revert w.
  revert C1.
  induction p ; intros C1 w ; simpl.
  - apply rew_step.
    revert C1 w.    
    induction r ; intros C1 w.
    + exact (App_l _ (IHr _ w)).
    + exact (App_r _ (IHr _ w)).
    + exact (CLam (IHr _ (Keep A1 w))).
    + apply CStep.
      induction r.
      * induction b.
        rewrite !wkTm_is_subTm.
        rewrite subTm_comp.
        unfold beta_sub.
        rewrite <- beta_sub_help.
        rewrite <- subTm_comp.
        apply AFSBeta.
        apply Beta.
      * rewrite !wkTm_is_subTm.
        rewrite !subTm_comp.
        apply AFSRew.
  - exact (rew_Trans (IHp1 C1 w) (IHp2 C1 w)).
Qed.

(** Rewriting is closed under substitution *)
Definition Rew_sub
           {B F : Type}
           {X : afs B F}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm X C2 A}
           (s : sub _ C1 C2)
           (p : t1 ∼> t2)
  : t1 [ s ] ∼> t2 [ s ].
Proof.
  revert s.
  revert C1.
  induction p ; intros C1 s ; simpl.
  - apply rew_step.
    revert C1 s.    
    induction r ; intros C1 s.
    + exact (App_l _ (IHr _ s)).
    + exact (App_r _ (IHr _ s)).
    + exact (CLam (IHr _ (keepSub A1 s))).
    + apply CStep.
      induction r.
      * induction b.
        simpl.
        apply AFSBeta.
        pose (Beta (subTm f (keepSub A1 s)) (subTm x s)) as p.
        unfold beta_sub in *.
        assert (f [ keepSub A1 s ] [ idSub C1 (arity X) && x [ s ] ]
                =
                f [ idSub C (arity X) && x ] [ s ])
          as H.
        {
          rewrite subTm_comp.
          unfold keepSub.
          rewrite dropSub_is_compSubWk.
          simpl ; cbn.
          rewrite <- compSub_compWkSub.
          simpl ; cbn.
          rewrite compWkSub_id.
          rewrite Sub_id_right.
          rewrite subTm_comp.
          simpl ; cbn.
          rewrite Sub_id_left.
          reflexivity.
        }
        rewrite H in p.
        exact p.
      * rewrite !subTm_comp.
        apply AFSRew.
  - exact (rew_Trans (IHp1 C1 s) (IHp2 C1 s)).
Qed.
