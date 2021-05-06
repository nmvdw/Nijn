Require Import Prelude.Basics.
Require Import Prelude.Funext.
Require Import Prelude.WellfoundedRelation.
Require Import Syntax.Signature.
Require Import Syntax.Signature.RewriteLemmas.
Require Import Coq.Program.Equality.

(** * The definition of beta normal forms (for single step relation) *)
Definition beta_nf
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : Prop
  := nf (fun (t1 t2 : tm ar C A) => t1 ~>β t2) t.


(** Relation between the two notions *)
Proposition beta_nf_step
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            {t : tm ar C A}
            (Ht : beta_nf t)
  : nf (fun (t1 t2 : tm ar C A) => t1 ~>β* t2) t.
Proof.
  intros t' r.
  induction r.
  - exact (Ht _ r).
  - apply IHr1.
    exact Ht.
Qed.

(** ** Base terms are strongly normalizing *)
Lemma baseTm_no_red_help
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      (t1 t2 : tm ar C A)
      (f : F)
      (p1 : ar f = A)
      (p2 : transport (tm ar C) p1 (BaseTm f) = t1)
  : t1 ~>β t2 -> False.
Proof.
  intro q.
  revert p2.
  revert p1.
  revert f.
  induction q ; intros f' p1 p2 ; try (subst ; simpl in * ; discriminate).
  - apply (is_BaseTm_transport (eq_sym p1) (λ f1)).
    rewrite <- p2.
    rewrite transport_sym_p.
    simpl.
    auto.
  - induction r.
    subst.
    simpl in *.
    discriminate.
Qed.

Lemma baseTm_no_red
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      (f : F)
      (t : tm ar C (ar f))
  : BaseTm f ~>β t -> False.
Proof.
  exact (baseTm_no_red_help (BaseTm f) t f eq_refl eq_refl).
Qed.

Lemma baseTm_beta_nf
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      (f : F)
  : @beta_nf _ _ ar C _ (BaseTm f).
Proof.
  intros t r.
  exact (baseTm_no_red f t r).
Qed.

(** ** Variables are strongly normalizing *)
Lemma var_beta_nf
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A : ty B}
      (v : var C A)
  : @beta_nf _ _ ar _ _ (TmVar v).
Proof.
  intros t r.
  dependent destruction r.
  inversion b.
Qed.

Proposition lam_beta_nf
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            (f : tm ar (A1 ,, C) A2)
            (Hf : beta_nf f)
  : beta_nf (λ f).
Proof.
  intros t' r.
  dependent destruction r.
  - exact (Hf _ r).
  - inversion b.
Qed.

Proposition from_lam_beta_nf
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            (f : tm ar (A1 ,, C) A2)
            (Hf : beta_nf (λ f))
  : beta_nf f.
Proof.
  intros t' r.
  refine (Hf (λ t') _).
  apply CLam.
  exact r.
Qed.

Proposition app_beta_nf
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            {f : tm ar C (A1 ⟶ A2)}
            (Hf1 : ~(is_Lambda f))
            (Hf2 : beta_nf f)
            {t : tm ar C A1}
            (Ht : beta_nf t)
  : beta_nf (f · t).
Proof.
  intros t' r.
  dependent destruction r.
  - contradiction (Hf2 _ r).
  - contradiction (Ht _ r).
  - dependent destruction b.
    simpl in Hf1.
    contradiction.
Qed.

Proposition from_app_beta_nf_help
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 A3 : ty B}
            {f : tm ar C A3}
            {t : tm ar C A1}
            (p : A3 = (A1 ⟶ A2))
            (H : beta_nf ((transport _ p f) · t))
  : ~(is_Lambda f).
Proof.
  intro H'.
  destruct f ; try (subst ; simpl in * ; contradiction).
  inversion p ; subst.
  rewrite (UIP p eq_refl) in H.
  exact (H _ (CStep (Beta _ _))).
Qed.

Proposition from_app_beta_nf
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            {f : tm ar C (A1 ⟶ A2)}
            {t : tm ar C A1}
            (H : beta_nf (f · t))
  : ~(is_Lambda f) /\ beta_nf f /\ beta_nf t.
Proof.
  repeat split.
  - exact (from_app_beta_nf_help eq_refl H).
  - intros f' r.
    refine (H (f' · t) _).
    apply App_l.
    exact r.
  - intros t' r.
    refine (H (f · t') _).
    apply App_r.
    exact r.
Qed.


(** * Normal forms as a mutual inductive type *)
Inductive nf {B : Type} {F : Type} (ar : F -> ty B) (C : con B) : ty B -> Type :=
| NeToNf : forall {A : ty B}, ne ar C A -> nf ar C A
| NfLam : forall {A1 A2 : ty B}, nf ar (A1 ,, C) A2 -> nf ar C (A1 ⟶ A2)
with ne {B : Type} {F : Type} (ar : F -> ty B) (C : con B) : ty B -> Type :=
| NeVar : forall {A : ty B}, var C A -> ne ar C A
| NeBaseTm : forall (f : F), ne ar C (ar f)
| NeApp : forall {A1 A2 : ty B}, ne ar C (A1 ⟶ A2) -> nf ar C A1 -> ne ar C A2.

Arguments NeToNf {_ _ _ _ _} _.
Arguments NfLam {_ _ _ _ _ _} _.
Arguments NeVar {_ _ _ _ _} _.
Arguments NeBaseTm {_ _ _ _} _.
Arguments NeApp {_ _ _ _ _ _} _ _.

(** Inclusion of normal forms into terms *)
Fixpoint nfToTm
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C : con B}
         {A : ty B}
         (t : nf ar C A)
  : tm ar C A
  := match t with
     | NeToNf t => neToTm t
     | NfLam f => Lam (nfToTm f)
     end
with neToTm
     {B : Type}
     {F : Type}
     {ar : F -> ty B}
     {C : con B}
     {A : ty B}
     (t : ne ar C A)
  : tm ar C A
  := match t with
     | NeVar v => TmVar v
     | NeBaseTm f => BaseTm f
     | NeApp f t => App (neToTm f) (nfToTm t)
     end.

(** Normal forms get mapped to normal forms *)
Fixpoint nfToTm_beta_nf
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C : con B}
         {A : ty B}
         (t : nf ar C A)
  : beta_nf (nfToTm t)
with neToTm_beta_nf
     {B : Type}
     {F : Type}
     {ar : F -> ty B}
     {C : con B}
     {A : ty B}
     (t : ne ar C A)
  : beta_nf (neToTm t) /\ ~(is_Lambda (neToTm t)).
Proof.
  - destruct t ; simpl.
    + apply neToTm_beta_nf.
    + apply lam_beta_nf.
      apply nfToTm_beta_nf.
  - destruct t ; simpl ; split ; try auto.
    + apply var_beta_nf.
    + apply baseTm_beta_nf.
    + apply app_beta_nf.
      * apply neToTm_beta_nf.
      * apply neToTm_beta_nf.
      * apply nfToTm_beta_nf.
Qed.

(** The other direction *)
Definition beta_nf_to_nf
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : (beta_nf t -> nf ar C A) * (beta_nf t /\ ~(is_Lambda t) -> ne ar C A).
Proof.
  induction t as [ ? f | ? ? v | ? ? ? f IHf | ? ? ? f IHf t IHt ] ; simpl ; split.
  - exact (fun _ => NeToNf (NeBaseTm f)).
  - exact (fun _ => NeBaseTm f).
  - exact (fun _ => NeToNf (NeVar v)).
  - exact (fun _ => NeVar v).
  - intro H.
    apply NfLam.
    apply IHf.
    apply from_lam_beta_nf.
    exact H.
  - intros [ ? ? ].
    contradiction.
  - intros H.
    apply NeToNf.
    pose (H' := from_app_beta_nf H).
    refine (NeApp _ _).
    + apply IHf ; split.
      * apply H'.
      * apply H'.
    + apply IHt.
      apply H'.
  - intros [ H ? ].
    pose (H' := from_app_beta_nf H).
    refine (NeApp _ _).
    + apply IHf ; split.
      * apply H'.
      * apply H'.
    + apply IHt.
      apply H'.
Defined.

(** Now we show these two maps are inverses *)
Proposition nfToTm_on_ne
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            (t : tm ar C A)
            (H : beta_nf t)
            (H' : ~ is_Lambda t)
  : fst (beta_nf_to_nf t) H = NeToNf (snd (beta_nf_to_nf t) (conj H H')).
Proof.
  induction t ; try reflexivity.
  simpl in *.
  contradiction.
Qed.

Fixpoint nfToTm_to_nf
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C : con B}
         {A : ty B}
         (t : nf ar C A)
  : forall (H : beta_nf (nfToTm t)),
    fst (beta_nf_to_nf (nfToTm t)) H = t
with neToTm_to_ne
     {B : Type}
     {F : Type}
     {ar : F -> ty B}
     {C : con B}
     {A : ty B}
     (t : ne ar C A)
  : forall (H : beta_nf (neToTm t) /\ ~ is_Lambda (neToTm t)),
    snd (beta_nf_to_nf (neToTm t)) H = t.
Proof.
  - destruct t ; simpl.
    + intros.
      etransitivity.
      {
        simple refine (nfToTm_on_ne _ _ _).
        apply neToTm_beta_nf.
      }
      f_equal.
      apply neToTm_to_ne.
    + intro H.
      f_equal.
      apply nfToTm_to_nf.
  - destruct t.
    + reflexivity.
    + reflexivity.
    + simpl.
      intro H.
      destruct H.
      f_equal.
      * apply neToTm_to_ne.
      * apply nfToTm_to_nf.
Qed.

Proposition beta_nf_to_nf_to_beta_nf
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            (t : tm ar C A)
  : (forall (H : beta_nf t), nfToTm (fst (beta_nf_to_nf t) H) = t)
    /\
    (forall (H : beta_nf t /\ ~(is_Lambda t)), neToTm (snd (beta_nf_to_nf t) H) = t).
Proof.
  induction t ; split ; simpl ; try reflexivity.
  - intro H.
    f_equal.
    apply IHt.
  - intro H.
    destruct H.
    contradiction.
  - intro.
    f_equal.
    + apply IHt1.
    + apply IHt2.
  - intro.
    destruct H ; simpl.
    f_equal.
    + apply IHt1.
    + apply IHt2.
Qed.

(** * We can also define when terms are strongly normalizing according to beta reduction *)
Definition term_is_beta_SN
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : Prop
  := isWf (fun (t1 t2 : tm ar C _) => t1 ~>β* t2) t.

Definition beta_nf_isSN
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           {t : tm ar C A}
           (Ht : beta_nf t)
  : term_is_beta_SN t.
Proof.
  apply acc.
  intros t' r.
  contradiction (beta_nf_step Ht _ r).
Qed.

(** ** Base terms and variables are strongly normalizing *)
Proposition baseTm_is_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            (f : F)
  : @term_is_beta_SN _ _ ar C _ (BaseTm f).
Proof.
  apply beta_nf_isSN.
  exact (baseTm_beta_nf f).
Qed.

Proposition var_is_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            (v : var C A)
  : @term_is_beta_SN _ _ ar _ _ (TmVar v).
Proof.
  apply beta_nf_isSN.
  exact (var_beta_nf v).
Qed.

Proposition wkTm_is_beta_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A : ty B}
            (t : tm ar C2 A)
            (p : term_is_beta_SN t)
  : term_is_beta_SN (wkTm t w).
Proof.
  induction p as [t Ht IHt].
  apply acc.
  intros t' r.
  pose (wkTm_red w (exist _ t eq_refl) r) as H.
  destruct H as [[wt' H] p].
  subst.
  apply IHt.
  exact p.
Qed.

(** ** Strongly normalizing terms reduce to strongly normalizing terms *)
Proposition red_to_beta_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            {t1 t2 : tm ar C A}
            (Ht : term_is_beta_SN t1)
            (r : t1 ~>β* t2)
  : term_is_beta_SN t2.
Proof.
  revert t2 r.
  induction Ht as [t Ht IHt].
  intros t2 r.
  apply acc.
  intros ? r'.
  apply (IHt t2 r).
  exact r'.
Qed.

(** ** If each single step reduction from a certain term leads to a strongly, then that term was also strongly normalizing *)
Proposition single_step_SN
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            (t : tm ar C A)
            (H : forall (t' : tm ar C A), t ~>β t' -> term_is_beta_SN t')
  : term_is_beta_SN t.
Proof.
  apply acc.
  intros t' r.
  induction r as [ ? ? r | ? ? ? r1 IHr1 r2 IHr2 ].
  - apply H.
    exact r.
  - apply IHr2.
    intros t' Ht'.
    apply IHr1.
    + apply H.
    + apply betaRed_step.
      exact Ht'.
Qed.
