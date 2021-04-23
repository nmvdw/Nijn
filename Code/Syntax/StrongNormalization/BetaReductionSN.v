Require Import Prelude.Basics.
Require Import Prelude.Wellfounded.
Require Import Syntax.Signature.
Require Import Syntax.Signature.SubstitutionLemmas.
Require Import Syntax.StrongNormalization.SN.
Require Import Coq.Program.Equality.

(** * Strongly normalizing terms *)
Definition term_isSN
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : Prop
  := isWf (fun (t1 t2 : tm ar C _) => betaRed t1 t2) t.

(** Base terms and variables are strongly normalizing *)
Lemma is_BaseTm_transport
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      (p : A1 = A2)
      (t : tm ar C A1)
  : is_BaseTm (transport _ p t) -> is_BaseTm t.
Proof.
  subst.
  exact (fun x => x).
Qed.

Lemma baseTm_is_nf_help
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      (t1 t2 : tm ar C A)
      (f : F)
      (p1 : ar f = A)
      (p2 : transport (tm ar C) p1 (BaseTm f) = t1)
  : betaRed t1 t2 -> False.
Proof.
  intro q.
  revert p2.
  revert p1.
  revert f.
  induction q ; intros f' p1 p2.
  - apply (IHq1 f' p1 p2).
  - subst.
    discriminate p2.
  - subst.
    discriminate p2.
  - apply (is_BaseTm_transport (eq_sym p1) (λ f1)).
    rewrite <- p2.
    rewrite transport_sym_p.
    simpl.
    auto.
  - subst.
    cbn in *.
    discriminate p2.
Qed.

Lemma baseTm_is_nf
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      (f : F)
      (t : tm ar C (ar f))
  : betaRed (BaseTm f) t -> False.
Proof.
  exact (baseTm_is_nf_help (BaseTm f) t f eq_refl eq_refl).
Qed.

Proposition baseTm_is_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            (f : F)
  : @term_isSN _ _ ar C _ (BaseTm f).
Proof.
  unfold term_isSN.
  apply acc.
  intros ? p.
  contradiction (baseTm_is_nf f _ p).
Qed.

Lemma var_is_nf
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      (v : var C A)
      (t : tm ar C A)
  : betaRed (TmVar v) t -> False.
Proof.
  intro p.
  dependent induction p.
  apply (IHp1 v).
  reflexivity.
Qed.

Proposition var_is_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            (v : var C A)
  : @term_isSN _ _ ar _ _ (TmVar v).
Proof.
  apply acc.
  intros ? q.
  contradiction (var_is_nf v _ q).
Qed.

(** Closed under weakening *)
Definition betaRed_wkTm
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {w : wk C1 C2}
           {A : ty B}
           {t2 : tm ar C2 A}
           {t1 : tm ar C1 A}
           (r : betaRed (wkTm t2 w) t1)
  : { t' : tm ar C2 A | t1 = wkTm t' w }.
Proof.
  (*
  revert r.
  revert t1.
  revert w.
  revert C1.
  induction t2 ; simpl in * ; intros C1 w t1 r.
  - contradiction (@baseTm_is_nf B F ar C1 f _ r).
  - admit.
  - admit.
  - specialize (IHt2_1 _ w).
    specialize (IHt2_2 _ w).

      
  dependent induction r.
  - specialize (IHr1 _ w t2 eq_refl).
    destruct IHr1 as [ t1' Ht1'].
    exact (IHr2 _ w t1' Ht1').
  - specialize (IHr _ w).
    admit.
  - specialize (IHr _ w).
    admit.
  - admit.
  - admit.
   *)
Admitted.

(*
Proposition betaRed_wkTm_from_red
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A : ty B}
            {t1 : tm ar C1 A}
            {t2 : tm ar C2 A}
            (r : betaRed (wkTm t2 w) t1)
  : betaRed t2 (betaRed_wkTm r).
Proof.
Admitted.

Proposition betaRed_wkTm_to_red
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A : ty B}
            {t1 : tm ar C1 A}
            {t2 : tm ar C2 A}
            (r : betaRed (wkTm t2 w) t1)
  : betaRed (wkTm (betaRed_wkTm r) w) t1.
Proof.
Admitted.
 *)

Proposition wkTm_isSN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A : ty B}
            (t : tm ar C2 A)
            (p : term_isSN t)
  : term_isSN (wkTm t w).
Proof.
  induction p as [t Ht IHt].
  apply acc.
  intros y r.
  (*
  pose (t' := betaRed_wkTm r).
  destruct t' as [t' Ht'].
  subst.
  apply IHt.
   *)
Admitted.

(** * Logical relations *)

(** On terms *)
Fixpoint logical_SN
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C : con B}
         {A : ty B}
  : tm ar C A -> Prop
  := match A with
     | Base b => term_isSN
     | A1 ⟶ A2 =>
       fun f =>
         forall (C2 : con B)
                (w : wk C2 C)
                (t : tm ar C2 A1),
           logical_SN t -> logical_SN (wkTm f w · t)
     end.

(** Preservation under weakening *)
Proposition wk_logical_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A : ty B}
            (t : tm ar C2 A)
            (Ht : logical_SN t)
  : logical_SN (wkTm t w).
Proof.
  destruct A.
  - apply wkTm_isSN.
    exact Ht.
  - intros C w' t' Ht'.
    rewrite wkTm_comp.
    exact (Ht _ (compWk w w') t' Ht').
Qed.

(** On substitutions *)
Definition logical_SN_sub
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           (s : sub ar C1 C2)
  : Prop
  := forall (A : ty B)
            (v : var C2 A),
    logical_SN (subVar v s).

(** Some constructions for logical substitutions *)
Proposition ToEmpty_logical_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            (C : con B)
  : logical_SN_sub (@ToEmpty _ _ ar C).
Proof.
  intros A v.
  inversion v.
Qed.

Proposition Extend_logical_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            {s : sub ar C1 C2}
            {A : ty B}
            (t : tm ar C1 A)
            (p : logical_SN_sub s)
            (q : logical_SN t)
  : logical_SN_sub (s & t).
Proof.
  intros A' v.
  dependent induction v ; simpl ; cbn.
  - exact q.
  - apply p.
Qed.

Proposition Extend_logical_SN_pr1
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            {s : sub ar C1 C2}
            {A : ty B}
            (t : tm ar C1 A)
            (p : logical_SN_sub (s & t))
  : logical_SN_sub s.
Proof.
  intros A' v.
  assert (subVar v s
          =
          subTm (TmVar (wkVar v (dropId C2 _))) (s & t)).
  {
    rewrite wkVar_is_subVar.
    symmetry.
    etransitivity.
    {
      apply (subTm_comp (TmVar v)).
    }
    simpl.
    f_equal.
    rewrite dropSub_is_compSubWk.
    rewrite <- compSub_compWkSub.
    simpl ; cbn.
    rewrite wkToSub_id.
    rewrite Sub_id_left.
    rewrite compWkSub_id.
    reflexivity.
  }
  rewrite H.
  apply p.
Qed.

Proposition Extend_logical_SN_pr2
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            {s : sub ar C1 C2}
            {A : ty B}
            (t : tm ar C1 A)
            (p : logical_SN_sub (s & t))
  : logical_SN t.
Proof.
  exact (p A Vz).
Qed.

(** * Neutral terms *)
Inductive is_neutral
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          {C : con B}
  : forall {A : ty B}, tm ar C A -> Prop
  :=
| BaseTm_is_neutral : forall (f : F), is_neutral (BaseTm f)
| Var_is_neutral : forall {A : ty B} (v : var C A), is_neutral (TmVar v)
| App_is_neutral : forall {A1 A2 : ty B} (f : tm ar C (A1 ⟶ A2)) (t : tm ar C A1),
    is_neutral f -> term_isSN t -> is_neutral (f · t).

Lemma beta_red_term_isSN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      {t1 t2 : tm ar C A}
      (r : betaRed t1 t2)
      (Ht1 : term_isSN t1)
  : term_isSN t2.
Proof.
  revert r.
  revert t2.
  induction Ht1 as [t1 Ht1 IHt1].
  intros t2 r.
  apply acc.
  intros t' r'.
  exact (IHt1 t2 r t' r').
Qed.

Lemma beta_red_neutral
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      {t1 t2 : tm ar C A}
      (r : betaRed t1 t2)
      (Ht1 : is_neutral t1)
  : is_neutral t2.
Proof.
  induction r.
  - apply IHr2.
    apply IHr1.
    exact Ht1.
  - dependent destruction Ht1.
    constructor.
    + apply IHr ; assumption.
    + assumption.
  - dependent destruction Ht1.
    constructor.
    + assumption.
    + exact (beta_red_term_isSN r H).
  - inversion Ht1.
  - dependent destruction Ht1.
    inversion Ht1.
Qed.

Lemma wk_neutral
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C1 C2 : con B}
      (w : wk C1 C2)
      {A : ty B}
      (t : tm ar C2 A)
      (p : is_neutral t)
  : is_neutral (wkTm t w).
Proof.
  induction t.
  - constructor.
  - constructor.
  - inversion p.
  - simpl in *.
    dependent destruction p.
    constructor.
    + apply IHt1.
      assumption.
    + apply wkTm_isSN.
      exact H.
Qed.

Definition map_tm_logical_SN
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (f : tm ar C (A1 ⟶ A2))
  : tm ar (A1 ,, C) A2
  := wkTm f (Drop _ (idWk C)) · TmVar Vz.

Definition BetaRed_Wk
           {B F : Type}
           {ar : F -> ty B}
           {C1 C2 : con B}
           {A : ty B}
           {t1 t2 : tm ar C2 A}
           (w : wk C1 C2)
           (p : betaRed t1 t2)
  : betaRed (wkTm t1 w) (wkTm t2 w).
Proof.
  revert w.
  revert C1.
  induction p ; intros C1 w ; simpl.
  - exact (BetaTrans (IHp1 C1 w) (IHp2 C1 w)).
  - exact (BetaRew_App_l _ (IHp C1 w)).
  - exact (BetaRew_App_r _ (IHp C1 w)).
  - exact (BetaRew_Lam (IHp _ (Keep A1 w))).
  - simpl.
    rewrite !wkTm_is_subTm.
    rewrite subTm_comp.
    unfold beta_sub.
    rewrite <- beta_sub_help.
    rewrite <- subTm_comp.
    apply BetaBeta.
Qed.

Lemma Rew_map_tm_logical_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      {f1 f2 : tm ar C (A1 ⟶ A2)}
      (p : betaRed f1 f2)
  : betaRed (map_tm_logical_SN f1) (map_tm_logical_SN f2).
Proof.
  unfold map_tm_logical_SN.
  apply BetaRew_App_l.
  apply BetaRed_Wk.
  exact p.
Qed.

Lemma neutral_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      (f : tm ar C (A1 ⟶ A2))
      (Hf1 : is_neutral f)
      (Hf2 : term_isSN f)
      (t : tm ar C A1)
      (Ht : term_isSN t)
  : term_isSN (f · t).
Proof.
  revert Hf1 Hf2.
  revert f.
  induction Ht as [t Ht IHt].
  intros f Hf1 Hf2.
  induction Hf2 as [f Hf2 IHf].
  apply acc.
  intros y r.
  dependent destruction r.
  - (*assert (f' : tm ar C (A1 ⟶ A)) by admit.
    assert (t' : tm ar C A1) by admit.
    assert (p : t3 = f' · t') by admit.
    assert (H : betaRed t t' + betaRed t t') by admit.
    subst.
    destruct H.
    + apply IHt.
      apply (IHf f').
     *)
    admit.
  - apply (IHf f2 r).
    exact (beta_red_neutral r Hf1).
  - apply (IHt x2 r).
    + exact Hf1.
    + apply acc.
      exact Hf2.
  - inversion Hf1.
Admitted.

(** * Properties of the logical relation *)

(** We prove two properties of logical relations, namely that neutral terms satisfy it and that each element that satisfies the relation, is strongly normalizing. We do that by mutual induction. *)
Lemma neutral_is_logical_SN_and_logical_SN_to_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {A : ty B}
  : forall {C : con B}
           (t : tm ar C A),
    (is_neutral t -> logical_SN t)
    /\
    (logical_SN t -> term_isSN t).
Proof.      
  induction A as [ b | A1 IHA1 A2 IHA2 ].
  - simpl.
    intros C t.
    split ; intro p.
    + induction p.
      * apply baseTm_is_SN.
      * apply var_is_SN.
      * apply neutral_SN ; assumption.
    + assumption.
  - simpl.
    intros C t.
    split ; intro p.
    + simpl.
      intros C' w t' q.
      apply IHA2.
      constructor.
      * apply wk_neutral.
        exact p.
      * apply IHA1.
        exact q.
    + simpl in p.
      pose (x := wkTm t (Drop A1 (idWk C)) · TmVar Vz).
      specialize (IHA2 _ x).
      unfold map_tm_logical_SN in IHA2.
      assert (logical_SN (wkTm t (Drop A1 (idWk C)) · TmVar Vz)) as w.
      {
        apply p.
        apply IHA1.
        constructor.
      }
      destruct IHA2 as [q IHA2].
      clear IHA1 q.
      specialize (IHA2 w).
      clear p.
      clear w.
      dependent induction IHA2.
      apply acc.
      intros y Hy.
      apply (H0 (map_tm_logical_SN y)) ; auto.
      apply Rew_map_tm_logical_SN.
      exact Hy.
Qed.

(** Accessors for these properties *)
Proposition logical_SN_to_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {A : ty B}
  : forall {C : con B}
           {t : tm ar C A}
           (p : logical_SN t),
    term_isSN t.
Proof.
  intros C t p.
  apply (neutral_is_logical_SN_and_logical_SN_to_SN t).
  exact p.
Qed.

Proposition neutral_is_logical_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {A : ty B}
  : forall {C : con B}
           (t : tm ar C A)
           (p : is_neutral t),
    logical_SN t.
Proof.
  intros C t p.
  apply (neutral_is_logical_SN_and_logical_SN_to_SN t).
  exact p.
Qed.

(** Now we can conclude that variables and base terms satisfy the logical relation *)
Lemma var_is_logical_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {A : ty B}
      {C : con B}
      (v : var C A)
  : @logical_SN _ _ ar _ _ (TmVar v).
Proof.
  apply neutral_is_logical_SN ; cbn.
  constructor.
Qed.

Lemma base_is_logical_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      (f : F)
  : @logical_SN _ _ ar C _ (BaseTm f).
Proof.
  apply neutral_is_logical_SN ; cbn.
  constructor.
Qed.

(** * Closure under beta *)

(** We first define repeat applications. This is basically just a list of terms where they types agree. Note that [repeat_app ar C A1 A2] is a repeated application of a term of type [A1] and it gives a term of type [A2]. *)
Inductive repeat_app
          {B : Type}
          {F : Type}
          (ar : F -> ty B)
          (C : con B)
  : ty B -> ty B -> Type
  :=
  | empty : forall (A : ty B), repeat_app ar C A A
  | add_term : forall (A1 A2 A3 : ty B),
      tm ar C A2
      -> repeat_app ar C A1 (A2 ⟶ A3)
      -> repeat_app ar C A1 A3.

Arguments empty {_ _ _ _ _}.
Arguments add_term {_ _ _ _ _ _ _} _ _.

(** The semantics of a repeated application *)
Fixpoint sem
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C : con B}
         {A1 A2 : ty B}
         (ps : repeat_app ar C A1 A2)
  : tm ar C A1 -> tm ar C A2
  := match ps with
     | empty => fun t => t
     | add_term t qs => fun f => sem qs f · t
     end.

(** Closure under weakening *)
Fixpoint wk_repeat_app
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C1 C2 : con B}
         {A1 A2 : ty B}
         (ps : repeat_app ar C2 A1 A2)
         (w : wk C1 C2)
  : repeat_app ar C1 A1 A2
  := match ps with
     | empty => empty
     | add_term t qs => add_term (wkTm t w) (wk_repeat_app qs w)
     end.

Proposition sem_wk_repeat_app
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            {A1 A2 : ty B}
            (ps : repeat_app ar C2 A1 A2)
            (w : wk C1 C2)
            (t : tm ar C2 A1)
  : sem (wk_repeat_app ps w) (wkTm t w) = wkTm (sem ps t) w.
Proof.
  induction ps as [ | ? ? ? t' qs IHqs ].
  - reflexivity.
  - simpl.
    rewrite IHqs.
    reflexivity.
Qed.

(** This lemma expresses that the logical relation is closed under beta reduction *)
Lemma logical_SN_beta_help
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 A3 : ty B}
      (f : tm ar (A1 ,, C) A2)
      (t : tm ar C A1)
      (Hsub : logical_SN (subTm f (beta_sub t)))
      (Hf : logical_SN f)
      (Ht : term_isSN t)
      (ps : repeat_app ar C A2 A3)
  : logical_SN (sem ps (λ f · t)).
Proof.
  revert ps Ht Hf Hsub.
  revert t f.
  revert A1 A2.
  revert C.
  induction A3 as [ b | A31 IHA31 A32 IHA32 ] ; intros C A1 A2 t f ps Ht Hf Hsub.
  - simpl.
    admit.
  - intros ? w t' Ht'.
    specialize (IHA32
                  _ _ _
                  (wkTm t w) (wkTm f (Keep A1 w))
                  (add_term t' (wk_repeat_app ps w))).
    simpl in IHA32.
    rewrite <- sem_wk_repeat_app.
    apply IHA32.
    + apply wkTm_isSN.
      exact Ht.
    + apply wk_logical_SN.
      exact Hf.
    + rewrite wkTm_is_subTm.
      rewrite subTm_comp.
      simpl ; cbn.
      rewrite dropSub_is_compSubWk.
      rewrite <- compSub_compWkSub.
      simpl ; cbn.
      rewrite compWkSub_id.
      rewrite Sub_id_right.
      unfold beta_sub in Hf.
      pose (wk_logical_SN w _ Hsub) as l.
      rewrite wkTm_is_subTm in l.
      rewrite subTm_comp in l.
      simpl in l.
      rewrite Sub_id_left in l.
      rewrite <- wkTm_is_subTm in l.
      exact l.
Admitted.

Lemma logical_SN_beta
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      (f : tm ar (A1 ,, C) A2)
      (t : tm ar C A1)
      (Hsub : logical_SN (subTm f (beta_sub t)))
      (Hf : logical_SN f)
      (Ht : term_isSN t)
  : logical_SN (λ f · t).
Proof.
  exact (logical_SN_beta_help f t Hsub Hf Ht empty).
Qed.

(** The fundamental theorem of logical relations *)
Theorem fundamental_thm_relations
        {B : Type}
        {F : Type}
        {ar : F -> ty B}
        {C1 C2 : con B}
        (s : sub ar C1 C2)
        {A : ty B}
        (t : tm ar C2 A)
        (p : logical_SN_sub s)
  : logical_SN (subTm t s).
Proof.
  revert p.
  revert s.
  revert C1.
  induction t ; intros C1 s p.
  - simpl.
    apply base_is_logical_SN.
  - simpl.
    induction s.
    + inversion v.
    + dependent induction v ; simpl ; cbn.
      * simpl in p.
        exact (Extend_logical_SN_pr2 _ p).
      * apply IHs.
        exact (Extend_logical_SN_pr1 _ p).
  - simpl.
    intros x w t' Ht'.
    apply logical_SN_beta.
    + rewrite wkTm_is_subTm.
      rewrite !subTm_comp.
      unfold beta_sub.
      simpl ; cbn.
      rewrite !dropSub_is_compSubWk.
      rewrite <- !compSub_compWkSub.
      simpl ; cbn.
      rewrite compWkSub_id.
      rewrite compWkSub_id.
      rewrite Sub_id_right.
      apply IHt.
      apply Extend_logical_SN ; try assumption.
      intros ? v.
      specialize (p _ v).
      rewrite <- subVar_comp.
      rewrite <- wkTm_is_subTm.
      apply wk_logical_SN.
      assumption.
    + rewrite wkTm_is_subTm.
      rewrite subTm_comp.
      apply IHt.
      simpl ; cbn ; unfold keepSub.
      rewrite !dropSub_is_compSubWk.
      rewrite <- !compSub_compWkSub.
      simpl ; cbn.
      rewrite compWkSub_id.
      apply Extend_logical_SN.
      * intros ? v.
        rewrite <- dropSub_is_compSubWk.
        rewrite <- subVar_comp.
        pose (wkTm_is_subTm (subVar v s) (Drop A1 w)) as q.
        simpl in q.
        rewrite <- q ; clear q.
        apply wk_logical_SN.
        apply p.
      * apply var_is_logical_SN.
    + apply logical_SN_to_SN.
      exact Ht'.
  - specialize (IHt2 _ s p).
    pose (IHt1 _ s p _ (idWk _) _ IHt2).
    rewrite wkTm_id in l.
    exact l.
Qed.

Lemma logical_SN_wk
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C1 C2 : con B}
      (w : wk C1 C2)
  : @logical_SN_sub _ _ ar _ _ (wkToSub w).
Proof.
  intros A v.
  rewrite <- wkVar_is_subVar.
  apply neutral_is_logical_SN.
  constructor.
Qed.

Lemma idSub_is_logical_SN_sub
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
  : logical_SN_sub (idSub C ar).
Proof.
  rewrite <- wkToSub_id.
  apply logical_SN_wk.
Qed.

(** Now we can conclude SN of the STLC *)
Lemma all_is_logical_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      (t : tm ar C A)
  : logical_SN t.
Proof.
  pose (fundamental_thm_relations (idSub C ar) t) as l.
  rewrite subTm_id in l.
  apply l.
  apply idSub_is_logical_SN_sub.
Qed.

Theorem BetaRed_SN
        {B : Type}
        {F : Type}
        (ar : F -> ty B)
        (C : con B)
        (A : ty B)
  : Wf (fun (t1 t2 : tm ar C A) => betaRed t1 t2).
Proof.
  intro t.
  apply logical_SN_to_SN.
  apply all_is_logical_SN.
Qed.
