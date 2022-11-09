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

Local Open Scope type.

(** * Proving strong normalization of the STLC using logical relations *)

(** ** The logical relation on terms *)
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

(** Preservation under beta reduction steps *)
Proposition beta_red_logical_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            {t1 t2 : tm ar C A}
            (Ht1 : logical_SN t1)
            (r : t1 ∼>β t2)
  : logical_SN t2.
Proof.
  revert C t1 t2 Ht1 r.
  induction A as [ b | A1 IHA1 A2 IHA2 ].
  - simpl ; intros.
    refine (red_to_beta_SN Ht1 _).
    apply betaRed_step.
    exact r.
  - intros C f1 f2 Hf1 r C' w t Ht.
    refine (IHA2 _ (wkTm f1 w · t) (wkTm f2 w · t) _ _).
    + exact (Hf1 _ _ _ Ht).
    + apply App_l.
      apply betaRed_step_Wk.
      exact r.
Qed.

(** ** The logical relation on substitutions *)
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
  dependent destruction v ; simpl ; cbn.
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
          TmVar (wkVar v (dropId C2 _)) [ s && t ])
    as H.
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

(** ** Neutral terms *)

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
  induction t as [ | | | ? ? ? t1 IHt1 t2 IHt2  ].
  - constructor.
  - constructor.
  - inversion p.
  - simpl in *.
    dependent destruction p.
    constructor.
    + apply IHt1.
      assumption.
    + apply wkTm_is_beta_SN.
      assumption.
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
      (r : t ∼>β t')
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
    + refine (red_to_beta_SN _ (betaRed_step r)).
      assumption.
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
  revert t Ht.
  induction Hf2 as [f2 Hf2 IHf2].
  intros t Ht.
  induction Ht as [t Ht IHt].
  apply single_step_SN.
  intros t' r.
  dependent destruction r.
  - specialize (IHf2 f0 (betaRed_step r) (neutral_beta Hf1 r)).
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
  apply betaRed_Wk.
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
  induction A as [ b | A1 IHA1 A2 IHA2 ] ; simpl.
  - intros C t.
    split ; intro p.
    + induction p.
      * apply baseTm_is_SN.
      * apply var_is_SN.
      * apply neutral_beta_SN ; assumption.
    + assumption.
  - intros C t.
    split ; intro p.
    + intros C' w t' q.
      apply IHA2.
      constructor.
      * apply wk_neutral.
        exact p.
      * apply IHA1.
        exact q.
    + pose (x := wkTm t (Drop A1 (idWk C)) · TmVar Vz).
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
      clear p w.
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

Notation "f ·· ps" := (sem ps f) (at level 20).

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
  : wkTm t w ·· wk_repeat_app ps w = wkTm (t ·· ps) w.
Proof.
  induction ps as [ | ? ? ? ? ? qs IHqs ].
  - reflexivity.
  - simpl.
    rewrite IHqs.
    reflexivity.
Qed.

(** Repeated applications preserve the logical relation *)
Lemma sem_logical_SN
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      (ps : repeat_app ar C A1 A2)
      (t : tm ar C A1)
      (H : logical_SN t)
  : logical_SN (t ·· ps).
Proof.
  induction ps as [ | ? ? ? t' H' ps IHps ].
  - exact H.
  - intros ; simpl.
    specialize (IHps t H _ (idWk _) t' H').
    rewrite wkTm_id in IHps.
    exact IHps.
Qed.

Lemma app_is_not_lam
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      {t : tm ar C A1}
      (ps : repeat_app ar C A1 A2)
      (Ht : ~(is_Lambda t))
  : ~(is_Lambda (t ·· ps)).
Proof.
  destruct ps ; auto.
Qed.

(** ** Reduction of substitutions *)
(** Since substitutions are just a list of terms, we can also define reduction on them. Beta reduction of a substitution is a beta step on one of the terms. We will use this to study how terms rewrite after a beta step. *)
Inductive sub_red
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
  : forall {C1 C2 : con B}, sub ar C1 C2 -> sub ar C1 C2 -> Type
  :=
| ExtendSub_left : forall {C1 C2 : con B}
                          (s : sub ar C1 C2)
                          {A : ty B}
                          {t1 t2 : tm ar C1 A}
                          (r : t1 ∼>β t2),
    sub_red (s && t1) (s && t2)
| ExtendSub_right : forall {C1 C2 : con B}
                           (s1 s2 : sub ar C1 C2)
                           {A : ty B}
                           {t : tm ar C1 A},
    sub_red s1 s2 -> sub_red (s1 && t) (s2 && t).

Notation "s1 ∼>βs s2" := (sub_red s1 s2) (at level 70).

(** The reduction relation on some standard constructions *)
Definition dropSub_red
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           (A : ty B)
           {C1 C2 : con B}
           {s1 s2 : sub ar C1 C2}
           (r : s1 ∼>βs s2)
  : dropSub A s1 ∼>βs dropSub A s2.
Proof.
  induction r ; simpl.
  - constructor.
    apply betaRed_step_Wk.
    exact r.
  - constructor.
    exact IHr.
Qed.

Definition keepSub_red
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           (A : ty B)
           {C1 C2 : con B}
           {s1 s2 : sub ar C1 C2}
           (r : s1 ∼>βs s2)
  : keepSub A s1 ∼>βs keepSub A s2.
Proof.
  unfold keepSub.
  constructor.
  apply dropSub_red.
  exact r.
Qed.

Definition beta_sub_red
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           {t1 t2 : tm ar C A}
           (r : t1 ∼>β t2)
  : beta_sub t1 ∼>βs beta_sub t2.
Proof.
  unfold beta_sub.
  constructor.
  exact r.
Qed.

(** The next propositions say the possibilities if we substitute a variable for a term that can be rewritten *)
Proposition subVar_red_or_eq
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            {s1 s2 : sub ar C1 C2}
            (r : s1 ∼>βs s2)
            {A : ty B}
            (v : var C2 A)
  : subVar v s1 ∼>β* subVar v s2.
Proof.
  induction v.
  - dependent destruction r ; simpl ; cbn.
    + left.
      apply betaRed_step.
      assumption.
    + right.
      reflexivity.
  - dependent destruction r ; simpl ; cbn.
    + right.
      reflexivity.
    + exact (IHv _ _ r).
Qed.

Proposition subTm_red_or_eq
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            {s1 s2 : sub ar C1 C2}
            (r : s1 ∼>βs s2)
            {A : ty B}
            (t : tm ar C2 A)
  : t [ s1 ] ∼>β* t [ s2 ].
Proof.
  revert C1 s1 s2 r.
  induction t as [ b | ? ? v | ? ? ? f IHf | ? ? ? f IHf t IHt ]
  ; simpl ; intros C1 s1 s2 r.
  - right ; reflexivity.
  - apply subVar_red_or_eq.
    exact r.
  - specialize (IHf _ (keepSub _ s1) (keepSub _ s2) (keepSub_red _ r)).
    destruct IHf as [p | p].
    + left.
      apply beta_Lam.
      exact p.
    + right.
      rewrite p.
      reflexivity.
  - specialize (IHf _ _ _ r).
    specialize (IHt _ _ _ r).
    destruct IHf as [p | p], IHt as [q | q].
    + left.
      exact (beta_Trans (beta_App_l _ p) (beta_App_r _ q)).
    + left.
      rewrite q.
      apply beta_App_l.
      exact p.
    + left.
      rewrite p.
      apply beta_App_r.
      exact q.
    + right.
      rewrite p, q.
      reflexivity.    
Qed.

Proposition sub_beta_red_or_eq
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            (f : tm ar (A1 ,, C) A2)
            {t1 t2 : tm ar C A1}
            (r : t1 ∼>β t2)
  : f [ beta_sub t1 ] ∼>β* f [ beta_sub t2 ].
Proof.
  exact (subTm_red_or_eq (beta_sub_red r) f).
Qed.

(** ** Reduction of repeated applications *)
Inductive repeat_app_red
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          {C : con B}
  : forall {A1 A2 : ty B}, repeat_app ar C A1 A2 -> repeat_app ar C A1 A2 -> Type
  :=
| add_term_top : forall {A1 A2 A3 : ty B}
                        {t1 t2 : tm ar C A2}
                        (Ht1 : logical_SN t1)
                        (Ht2 : logical_SN t2)
                        (ps : repeat_app ar C A1 (A2 ⟶ A3)),
    t1 ∼>β t2
    ->
    repeat_app_red (add_term t1 Ht1 ps) (add_term t2 Ht2 ps)
| add_term_rest : forall {A1 A2 A3 : ty B}
                         {t : tm ar C A2}
                         (Ht : logical_SN t)
                         (ps qs : repeat_app ar C A1 (A2 ⟶ A3)),
    repeat_app_red ps qs
    ->
    repeat_app_red (add_term t Ht ps) (add_term t Ht qs).

Notation "ps ∼>βr qs" := (repeat_app_red ps qs) (at level 70).

(** Rewriting in a repeated application *)
Definition repeat_app_left
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (ps : repeat_app ar C A1 A2)
           {t1 t2 : tm ar C A1}
           (r : t1 ∼>β+ t2)
  : t1 ·· ps ∼>β+ t2 ·· ps.
Proof.
  induction ps as [ | ? ? ? ? ? ps IHps ] ; simpl.
  - exact r.
  - apply beta_App_l.
    apply IHps.
    exact r.
Qed.

Definition repeat_app_right
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (ps qs : repeat_app ar C A1 A2)
           {t : tm ar C A1}
           (r : ps ∼>βr qs)
  : t ·· ps ∼>β t ·· qs.
Proof.
  induction r as [ ? ? ? ? ? ? ? ? b | ? ? ? ? ? ? ? r IHr ] ; simpl.
  - apply App_r.
    exact b.
  - apply App_l.
    apply IHr.
Qed.

(** Beta reduction of repeated applications is well-founded *)
Definition repeat_app_red_Wf
           {B : Type}
           {F : Type}
           (ar : F -> ty B)
           (C : con B)
           (A1 A2 : ty B)
  : Wf (fun (ps1 ps2 : repeat_app ar C A1 A2) => ps1 ∼>βr ps2).
Proof.
  intro ps.
  induction ps as [ | ? ? ? t Ht ps IHps ].
  - apply acc.
    intros.
    inversion X.
  - revert t Ht.
    induction IHps as [ ps Hps IHps ].
    intros t Ht.
    pose (logical_SN_to_SN Ht) as Ht'.
    induction Ht' as [t ? IHt].
    apply acc.
    intros qs r.
    dependent destruction r.
    + apply IHt.
      apply betaRed_step.
      exact b.
    + apply IHps.
      exact r.
Qed.

(** Now we look at the shape of reductions in a repeated application and in a beta redex. *)
Definition red_repeat_app
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           {t : tm ar C A1}
           {ps : repeat_app ar C A1 A2}
           {u : tm ar C A2}
           (Ht : ~(is_Lambda t))
           (r : t ·· ps ∼>β u)
  : { t' : tm ar C A1 & (t ∼>β t') * (u = t' ·· ps)}
    + { ps' : repeat_app ar C A1 A2 & (ps ∼>βr ps') * (u = t ·· ps')}.
Proof.
  induction ps.
  - simpl in *.
    left.
    exists u.
    split ; try reflexivity.
    exact r.
  - simpl in *.
    dependent destruction r.
    + destruct (IHps t f2 Ht r).
      * left.
        destruct s as [x H].
        exists x.
        split.
        ** apply H.
        ** f_equal.
           apply H.
      * right.
        destruct s as [x H].
        exists (add_term t0 l x).
        simpl.
        split.
        ** apply add_term_rest.
           apply H.
        ** f_equal.
           apply H.
    + right.
      exists (add_term _ (beta_red_logical_SN l r) ps).
      split ; simpl.
      * apply add_term_top.
        exact r.
      * reflexivity.
    + pose (app_is_not_lam ps Ht) as n.
      simpl in n.
      dependent destruction b.
      rewrite <- x in n.
      simpl in n.
      contradiction.
Qed.

Definition red_beta_redex
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           {f : tm ar (A1 ,, C) A2}
           {t : tm ar C A1}
           {u : tm ar C A2}
           (r : (λ f · t) ∼>β u)
  : (u = f [ beta_sub t ])
    + { t' : tm ar C A1 & (t ∼>β t') * (u = λ f · t') }
    + { f' : tm ar (A1 ,, C) A2 & (f ∼>β f') * (u = λ f' · t)}.
Proof.
  dependent destruction r.
  - dependent destruction r.
    + right.
      exists f0.
      split ; try reflexivity.
      exact r.
    + dependent destruction r.
  - left ; right.
    exists x2.
    split ; try reflexivity.
    exact r.
  - dependent destruction b.
    left ; left.
    reflexivity.
Qed.

(** The next two lemmata express that the logical relation is closed under beta reduction *)
Lemma logical_SN_beta_help_base
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 A3 : ty B}
      (f : tm ar (A1 ,, C) A2)
      (t : tm ar C A1)
      (ps : repeat_app ar C A2 A3)
      (Hsub : term_is_beta_SN (f [ beta_sub t ] ·· ps))
      (Hf : term_is_beta_SN f)
      (Ht : term_is_beta_SN t)
  : term_is_beta_SN ((λ f · t) ·· ps).
Proof.
  revert t Ht ps Hsub.
  induction Hf as [f Hf IHf].
  intros t Ht.
  induction Ht as [t Ht IHt].
  intros ps Hsub.
  induction (repeat_app_red_Wf ar C A2 A3 ps) as [ps Hps IHps].
  apply single_step_SN ; intros t' r.
  assert (W : ~(is_Lambda (λ f · t))) by auto.
  destruct (red_repeat_app W r) as [ [u  [r' H]] | [ps' [ r' p ]] ].
  - destruct (red_beta_redex r') as [ [ p | [ u' [ p H' ]]] | [ f' [ p H' ]]].
    + subst.
      exact Hsub.
    + subst.
      apply (IHt u' (TStep p)).
      destruct (sub_beta_red_or_eq f p) as [q | q].
      * refine (red_to_beta_SN Hsub _).
        apply repeat_app_left.
        exact q.
      * rewrite <- q.
        exact Hsub.
    + subst.
      apply (IHf f' (TStep p) t).
      * apply acc ; assumption.
      * apply (red_to_beta_SN Hsub).
        apply repeat_app_left.
        apply betaRed_sub.
        apply TStep.
        exact p.
  - subst.
    apply IHps.
    + exact r'.
    + refine (red_to_beta_SN Hsub _).
      apply betaRed_step.
      apply repeat_app_right.
      exact r'.
Qed.

Lemma logical_SN_beta_help
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 A3 : ty B}
      (f : tm ar (A1 ,, C) A2)
      (t : tm ar C A1)
      (Hsub : logical_SN (f [ beta_sub t ]))
      (Hf : logical_SN f)
      (Ht : logical_SN t)
      (ps : repeat_app ar C A2 A3)
  : logical_SN ((λ f · t) ·· ps).
Proof.
  revert ps Ht Hf Hsub.
  revert t f.
  revert A1 A2.
  revert C.
  induction A3 as [ b | A31 IHA31 A32 IHA32 ] ; intros C A1 A2 t f ps Ht Hf Hsub.
  - simpl.
    pose (H := sem_logical_SN ps _ Hsub).
    apply logical_SN_beta_help_base ; apply logical_SN_to_SN ; assumption.
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
Qed.

Lemma logical_SN_beta
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      (f : tm ar (A1 ,, C) A2)
      (t : tm ar C A1)
      (Hsub : logical_SN (f [ beta_sub t ]))
      (Hf : logical_SN f)
      (Ht : logical_SN t)
  : logical_SN (λ f · t).
Proof.
  exact (logical_SN_beta_help f t Hsub Hf Ht empty).
Qed.

(** ** The fundamental theorem of logical relations *)
Theorem fundamental_thm_relations
        {B : Type}
        {F : Type}
        {ar : F -> ty B}
        {C1 C2 : con B}
        (s : sub ar C1 C2)
        {A : ty B}
        (t : tm ar C2 A)
        (p : logical_SN_sub s)
  : logical_SN (t [ s ]).
Proof.
  revert p.
  revert s.
  revert C1.
  induction t ; intros C1 s p ; simpl.
  - apply base_is_logical_SN.
  - induction s.
    + inversion v.
    + dependent induction v ; simpl ; cbn.
      * exact (Extend_logical_SN_pr2 _ p).
      * apply IHs.
        exact (Extend_logical_SN_pr1 _ p).
  - intros x w t' Ht'.
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

(** ** The STLC is SN *)
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
