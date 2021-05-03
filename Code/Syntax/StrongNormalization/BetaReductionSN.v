Require Import Prelude.Funext.
Require Import Prelude.Basics.
Require Import Prelude.WellfoundedRelation.
Require Import Prelude.TransitiveClosure.
Require Import Syntax.Signature.
Require Import Syntax.Signature.SubstitutionLemmas.
Require Import Syntax.Signature.RewriteLemmas.
Require Import Syntax.StrongNormalization.SN.
Require Import Syntax.StrongNormalization.BetaNormalForm.
Require Import Coq.Program.Equality.

(** On terms *)
Fixpoint logical_SN
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C : con B}
         {A : ty B}
  : tm ar C A -> Prop
  := match A with
     | Base b => term_is_beta_SN
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
  - simpl in *.
    apply wkTm_is_beta_SN.
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
  : logical_SN_sub (s && t).
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
            (p : logical_SN_sub (s && t))
  : logical_SN_sub s.
Proof.
  intros A' v.
  assert (subVar v s
          =
          subTm (TmVar (wkVar v (dropId C2 _))) (s && t)).
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
            (p : logical_SN_sub (s && t))
  : logical_SN t.
Proof.
  exact (p A Vz).
Qed.

(** * Neutral terms *)

(** Our goal is to show that all neutral terms satisfy the logical relation *)
Inductive is_neutral
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          {C : con B}
  : forall {A : ty B}, tm ar C A -> Type
  :=
| BaseTm_is_neutral : forall (f : F), is_neutral (BaseTm f)
| Var_is_neutral : forall {A : ty B} (v : var C A), is_neutral (TmVar v)
| App_is_neutral : forall {A1 A2 : ty B} (f : tm ar C (A1 ⟶ A2)) (t : tm ar C A1),
    is_neutral f -> term_is_beta_SN t -> is_neutral (f · t).

(** Neutral terms are closed under weakening *)
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
    + apply wkTm_is_beta_SN.
      exact t0.
Qed.


(** * Properties of the logical relation *)

(** We prove two properties of logical relations, namely that neutral terms satisfy it and that each element that satisfies the relation, is strongly normalizing. We do that by mutual induction. *)

(** Neutral terms reduce to neutral terms *)
Lemma neutral_beta
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      {t t' : tm ar C A}
      (Ht : is_neutral t)
      (r : t ~>β t')
  : is_neutral t'.
Proof.
  induction r.
  - dependent destruction Ht.
    apply App_is_neutral.
    + apply IHr.
      exact Ht.
    + exact t0.
  - dependent destruction Ht.
    apply App_is_neutral.
    + exact Ht.
    + clear IHr.
      revert r.
      revert x2.
      induction t0 as [x1 Hx1 IHx1].
      intros x2 r.
      apply single_step_SN.
      intros t' Ht'.
      exact (IHx1 x2 (TStep r) t' Ht').
  - inversion Ht.
  - induction r.
    dependent destruction Ht.
    inversion Ht.
Qed.

(** If we apply a strongly normalizing neutral term to a strongly normalizing term, then we get another strongly normalizing term *)
Lemma neutral_beta_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      (f : tm ar C (A1 ⟶ A2))
      (Hf1 : is_neutral f)
      (Hf2 : term_is_beta_SN f)
      (t : tm ar C A1)
      (Ht : term_is_beta_SN t)
  : term_is_beta_SN (f · t).
Proof.
  revert Ht.
  revert t.
  induction Hf2 as [f2 Hf2 IHf2].
  intros t Ht.
  induction Ht as [t Ht IHt].
  apply single_step_SN.
  intros t' r.
  dependent destruction r.
  - pose (X := neutral_beta Hf1 r).
    specialize (IHf2 f0 (TStep r) X).
    apply IHf2.
    apply acc ; assumption.
  - exact (IHt x2 (TStep r)).
  - dependent destruction b.
    inversion Hf1.
Qed.

(** Neutral terms satisfy the logical relation and terms that satisfy the logical relation are strongly normalizing *)
Definition map_tm_logical_SN
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (f : tm ar C (A1 ⟶ A2))
  : tm ar (A1 ,, C) A2
  := wkTm f (Drop _ (idWk C)) · TmVar Vz.

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
  apply beta_App_l.
  apply BetaRed_Wk.
  exact p.
Qed.

Lemma neutral_is_logical_SN_and_logical_SN_to_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {A : ty B}
  : forall {C : con B}
           (t : tm ar C A),
    (is_neutral t -> logical_SN t)
    /\
    (logical_SN t -> term_is_beta_SN t).
Proof.      
  induction A as [ b | A1 IHA1 A2 IHA2 ].
  - simpl.
    intros C t.
    split ; intro p.
    + induction p.
      * apply baseTm_is_SN.
      * apply var_is_SN.
      * apply neutral_beta_SN ; assumption.
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
    term_is_beta_SN t.
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
  | add_term : forall (A1 A2 A3 : ty B)
                      (t : tm ar C A2),
      logical_SN t
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
     | empty => fun f => f
     | add_term t _ qs => fun f => sem qs f · t
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
     | add_term t Ht qs => add_term (wkTm t w) (wk_logical_SN w _ Ht) (wk_repeat_app qs w)
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
  induction ps as [ | ? ? ? t' ? qs IHqs ].
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
      (Ht : logical_SN t)
      (ps : repeat_app ar C A2 A3)
  : logical_SN (sem ps (λ f · t)).
Proof.
  revert ps Ht Hf Hsub.
  revert t f.
  revert A1 A2.
  revert C.
  induction A3 as [ b | A31 IHA31 A32 IHA32 ] ; intros C A1 A2 t f ps Ht Hf Hsub.
  - simpl.
    assert (term_is_beta_SN (sem ps (subTm f (beta_sub t)))).
    {
      apply logical_SN_to_SN.
      (* make a separate lemma *)
      induction ps.
      - exact Hsub.
      - simpl.
        pose (IHps f Hf Hsub _ (idWk _) t0 l : logical_SN _).
        simpl in l0.
        rewrite wkTm_id in l0.
        exact l0.
    }

    admit.
  - intros ? w t' Ht'.
    specialize (IHA32
                  _ _ _
                  (wkTm t w) (wkTm f (Keep A1 w))
                  (add_term t' Ht' (wk_repeat_app ps w))).
    simpl in IHA32.
    rewrite <- sem_wk_repeat_app.
    apply IHA32.
    + apply wk_logical_SN.
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
      (Ht : logical_SN t)
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
    + exact Ht'.
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
