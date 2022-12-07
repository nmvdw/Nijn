Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.
Require Import Coq.Program.Equality.

(** * The subterm relation *)
Section SubTerm.
  Context {B F : Type}
          {ar : F -> ty B}.

  (** We define the subterm relation inductively. If two terms are equal, then they are subterms of each other. In addition, we can take subterms of application and lambda abstraction. *)
  Inductive subTerm
            {C₁ : con B}
            {A₁ : ty B}
            (t₁ : tm ar C₁ A₁)
    : forall {C₂ : con B} {A₂ : ty B} (t₂ : tm ar C₂ A₂), Type :=
  | EqSubTm : forall {C₂ : con B}
                     {A₂ : ty B}
                     (t₂ : tm ar C₂ A₂)
                     (p : C₁ = C₂)
                     (q : A₁ = A₂),
                transport (fun z => tm ar z _) p (transport (tm ar C₁) q t₁) = t₂
                ->
                subTerm t₁ t₂
  | SubAppL : forall {C₂ : con B}
                     {A₂ A₂' : ty B}
                     (f₂ : tm ar C₂ (A₂ ⟶ A₂'))
                     (t₂ : tm ar C₂ A₂),
                subTerm t₁ f₂ -> subTerm t₁ (f₂ · t₂)
  | SubAppR : forall {C₂ : con B}
                     {A₂ A₂' : ty B}
                     (f₂ : tm ar C₂ (A₂ ⟶ A₂'))
                     (t₂ : tm ar C₂ A₂),
                subTerm t₁ t₂ -> subTerm t₁ (f₂ · t₂)
  | SubLam : forall {C₂ : con B}
                     {A₂ A₂' : ty B}
                     (f₂ : tm ar (A₂ ,, C₂) A₂'),
               subTerm t₁ f₂ -> subTerm t₁ (λ f₂).

  Notation "t₁ ≼ t₂" := (subTerm t₁ t₂) (at level 50) : signature. (* \preceq *)

  (** The subterm relation is decidable. For that, we need several lemmas. *)
  Definition subTm_baseTm_help
             {C₁ C₂ : con B}
             {A₁ A₂ : ty B}
             (t₁ : tm ar C₁ A₁)
             (t₂ : tm ar C₂ A₂)
             (f : F)
             (p : A₂ = ar f)
             (q : transport _ p t₂ = BaseTm f)
             (H : t₁ ≼ t₂)
    : is_BaseTm_at f t₁.
  Proof.
    revert f p q.
    induction H as [ ? ? s₁ s₂ r
                   | ? ? ? ? ? H IHH
                   | ? ? ? ? ? H IHH
                   | ? ? ? ? H IHH ] ;
      intros f p q.
    - subst ; cbn in q ; subst.
      reflexivity.
    - subst ; cbn in q ; subst.
      discriminate.
    - subst ; cbn in q ; subst.
      discriminate.
    - assert (is_Lambda (BaseTm f : tm ar C₂ _)).
      {
        rewrite <- q.
        apply transport_Lambda.
        apply I.
      }
      contradiction.
  Qed.
  
  Definition subTm_baseTm
             {C₁ C₂ : con B}
             {A₁ : ty B}
             (t₁ : tm ar C₁ A₁)
             (f : F)
             (H : t₁ ≼ (BaseTm f : tm ar C₂ _))
    : is_BaseTm_at f t₁.
  Proof.
    exact (subTm_baseTm_help t₁ (BaseTm f : tm ar C₂ _) f (eq_refl _) (eq_refl _) H).
  Defined.

  Definition subTm_TmVar_help
             {C₁ C₂ : con B}
             {A₁ A₂ : ty B}
             (t₁ : tm ar C₁ A₁)
             (t₂ : tm ar C₂ A₂)
             (v : var C₂ A₂)
             (q : t₂ = TmVar v)
             (H : t₁ ≼ t₂)
    : is_TmVar t₁.
  Proof.
    revert v q.
    induction H as [ ? ? s₁ s₂ r
                   | ? ? ? ? ? H IHH
                   | ? ? ? ? ? H IHH
                   | ? ? ? ? H IHH ] ;
      intros v q.
    - subst ; cbn in q ; subst.
      reflexivity.
    - subst ; cbn in q ; subst.
      discriminate.
    - subst ; cbn in q ; subst.
      discriminate.
    - assert (is_Lambda (TmVar v : tm ar _ _)).
      {
        rewrite <- q.
        apply I.
      }
      contradiction.
  Qed.
  
  Definition subTm_TmVar
             {C₁ C₂ : con B}
             {A₁ A₂ : ty B}
             (t₁ : tm ar C₁ A₁)
             (v : var C₂ A₂)
             (H : t₁ ≼ TmVar v)
    : is_TmVar t₁.
  Proof.
    exact (subTm_TmVar_help t₁ (TmVar v) v (eq_refl _) H).
  Defined.

  Program Fixpoint dec_subTerm_Base
                   {C₁ C₂ : con B}
                   {A₁ : ty B}
                   `{decEq B}
                   `{decEq F}
                   (t₁ : tm ar C₁ A₁)
                   (f₂ : F)
    : (t₁ ≼ (BaseTm f₂ : tm ar C₂ _)) + (t₁ ≼ (BaseTm f₂ : tm ar C₂ _) -> False)
    := match t₁ with
       | BaseTm f₁ =>
         match dec_eq f₁ f₂ with
         | Yes p =>
           match dec_eq C₁ C₂ with
           | Yes q => inl _
           | No q => inr _
           end
         | No p => inr (fun q => _)
         end
       | TmVar v₁ => inr (fun q => subTm_baseTm _ _ q)
       | f₁ · t₁ => inr (fun q => subTm_baseTm _ _ q)
       | λ f₁ => inr (fun q => subTm_baseTm _ _ q)
       end.
  Next Obligation.
    refine (EqSubTm _ _ (eq_refl _) (eq_refl _) _).
    reflexivity.
  Qed.
  Next Obligation.
    inversion X.
    contradiction.
  Qed.
  Next Obligation.
    assert (f₁ = f₂).
    {
      symmetry.
      apply (subTm_baseTm _ _ q).
    }
    contradiction.
  Qed.

  Program Fixpoint dec_subTerm_TmVar
                   {C₁ C₂ : con B}
                   {A₁ A₂ : ty B}
                   `{decEq B}
                   `{decEq F}
                   (t₁ : tm ar C₁ A₁)
                   (v₂ : var C₂ A₂)
      : (t₁ ≼ TmVar v₂) + (t₁ ≼ TmVar v₂ -> False)
      := match t₁ with
         | BaseTm f₁ => inr (fun q => subTm_TmVar _  _ q)
         | TmVar v₁ =>
             match dec_eq C₁ C₂ with
             | Yes p =>
                 match dec_eq A₁ A₂ with
                 | Yes q =>
                     match dec_eq
                             (transport (fun z => var z _) p (transport (var C₁) q v₁))
                             v₂
                     with
                     | Yes r => inl (EqSubTm _ _ p q _)
                     | No r => inr _
                     end
                 | No q => inr _
                 end
             | No p => inr _
             end
         | f₁ · t₁ => inr (fun q => subTm_TmVar _  _ q)
         | λ f₁ => inr (fun q => subTm_TmVar _  _ q)
         end.
  Next Obligation.
    cbn in *.
    inversion X.
    subst.
    rewrite (UIP p (eq_refl _)) in H1.
    rewrite (UIP q (eq_refl _)) in H1.
    cbn in *.
    pose (from_path_in_sigma _ (from_path_in_sigma _ H1)) as p'.
    inversion p'.
    pose (from_path_in_sigma _ H3).
    contradiction.
  Qed.
  Next Obligation.
    cbn in *.
    inversion X.
    subst.
    rewrite (UIP p (eq_refl _)) in H1.
    cbn in *.
    pose (from_path_in_sigma _ (from_path_in_sigma _ H1)) as p'.
    inversion p'.
    pose (from_path_in_sigma _ H3).
    contradiction.
  Qed.
  Next Obligation.
    cbn in *.
    inversion X.
    subst.
    cbn in *.
    pose (from_path_in_sigma _ (from_path_in_sigma _ H1)) as p'.
    inversion p'.
    pose (from_path_in_sigma _ H3).
    contradiction.
  Qed.

  Proposition not_subTerm_app_1
              {C₁ C₂ : con B}
              {A₁ A₂ A₂' : ty B}
              {t₁ : tm ar C₁ A₁}
              {f₂ : tm ar C₂ (A₂ ⟶ A₂')}
              {t₂ : tm ar C₂ A₂}
              (H₁ : subTerm t₁ f₂ -> False)
              (H₂ : subTerm t₁ t₂ -> False)
              (H₃ : ~(C₁ = C₂))
    : subTerm t₁ (f₂ · t₂) -> False.
  Proof.
    intro H.
    dependent destruction H.
    - contradiction.
    - contradiction.
    - contradiction.
  Qed.

  Proposition not_subTerm_app_2
              {C₁ C₂ : con B}
              {A₁ A₂ A₂' : ty B}
              {t₁ : tm ar C₁ A₁}
              {f₂ : tm ar C₂ (A₂ ⟶ A₂')}
              {t₂ : tm ar C₂ A₂}
              (H₁ : subTerm t₁ f₂ -> False)
              (H₂ : subTerm t₁ t₂ -> False)
              (H₃ : ~(A₁ = A₂'))
    : subTerm t₁ (f₂ · t₂) -> False.
  Proof.
    intro H.
    dependent destruction H.
    - contradiction.
    - contradiction.
    - contradiction.
  Qed.

  Proposition not_subTerm_app_3
              {C₁ C₂ : con B}
              {A₁ A₂ A₂' : ty B}
              {t₁ : tm ar C₁ A₁}
              {f₂ : tm ar C₂ (A₂ ⟶ A₂')}
              {t₂ : tm ar C₂ A₂}
              (H₁ : subTerm t₁ f₂ -> False)
              (H₂ : subTerm t₁ t₂ -> False)
              {p : C₁ = C₂}
              {q : A₁ = A₂'}
              (H₃ : ~(transport (fun z => tm ar z _) p (transport (tm ar C₁) q t₁)
                      =
                      (f₂ · t₂)))
    : subTerm t₁ (f₂ · t₂) -> False.
  Proof.
    intro H.
    dependent destruction H.
    - subst.
      rewrite (UIP p0 (eq_refl _)) in e.
      rewrite (UIP q0 (eq_refl _)) in e.
      cbn in *.
      contradiction.
    - contradiction.
    - contradiction.
  Qed.

  Proposition not_subTerm_lam_1
              {C₁ C₂ : con B}
              {A₁ A₂ A₂' : ty B}
              {t₁ : tm ar C₁ A₁}
              {f₂ : tm ar (A₂ ,, C₂) A₂'}
              (H₁ : subTerm t₁ f₂ -> False)
              (H₃ : ~(C₁ = C₂))
    : subTerm t₁ (λ f₂) -> False.
  Proof.
    intro H.
    dependent destruction H.
    - contradiction.
    - contradiction.
  Qed.

  Proposition not_subTerm_lam_2
              {C₁ C₂ : con B}
              {A₁ A₂ A₂' : ty B}
              {t₁ : tm ar C₁ A₁}
              {f₂ : tm ar (A₂ ,, C₂) A₂'}
              (H₁ : subTerm t₁ f₂ -> False)
              (H₃ : ~(A₁ = (A₂ ⟶ A₂')))
    : subTerm t₁ (λ f₂) -> False.
  Proof.
    intro H.
    dependent destruction H.
    - contradiction.
    - contradiction.
  Qed.

  Proposition not_subTerm_lam_3
              {C₁ C₂ : con B}
              {A₁ A₂ A₂' : ty B}
              {t₁ : tm ar C₁ A₁}
              {f₂ : tm ar (A₂ ,, C₂) A₂'}
              (H₁ : subTerm t₁ f₂ -> False)
              {p : C₁ = C₂}
              {q : A₁ = (A₂ ⟶ A₂')}
              (H₃ : ~(transport (fun z => tm ar z _) p (transport (tm ar C₁) q t₁)
                      =
                      (λ f₂)))
    : subTerm t₁ (λ f₂) -> False.
  Proof.
    intro H.
    dependent destruction H.
    - subst.
      rewrite (UIP p0 (eq_refl _)) in *.
      rewrite (UIP q0 (eq_refl _)) in *.
      cbn in *.
      contradiction.
    - contradiction.
  Qed.

  Fixpoint dec_subTerm
           {C₁ C₂ : con B}
           {A₁ A₂ : ty B}
           `{decEq B}
           `{decEq F}
           (t₁ : tm ar C₁ A₁)
           (t₂ : tm ar C₂ A₂)
    : (t₁ ≼ t₂) + (t₁ ≼ t₂ -> False)
    := match t₂ with
       | BaseTm f₂ => dec_subTerm_Base t₁ f₂
       | TmVar v₂ => dec_subTerm_TmVar t₁ v₂
       | @App _ _ _ _ _ A₂ f₂ t₂ =>
         match dec_subTerm t₁ f₂ with
         | inl p => inl (SubAppL _ _ _ p)
         | inr r₁ =>
           match dec_subTerm t₁ t₂ with
           | inl p => inl (SubAppR _ _ _ p)
           | inr r₂ =>
             match dec_eq C₁ C₂ with
             | Yes p =>
               match dec_eq A₁ A₂ with
               | Yes q =>
                   match dec_eq
                           (transport (fun z => tm ar z _) p (transport (tm ar C₁) q t₁))
                           (f₂ · t₂)
                   with
                   | Yes r => inl (EqSubTm _ _ p q r)
                   | No r₃ => inr (not_subTerm_app_3 r₁ r₂ r₃)
                   end
               | No r₃ => inr (not_subTerm_app_2 r₁ r₂ r₃)
               end
             | No r₃ => inr (not_subTerm_app_1 r₁ r₂ r₃)
             end
           end
         end
       | @Lam _ _ _ _ A₂ A₂' f₂ =>
         match dec_subTerm t₁ f₂ with
         | inl p => inl (SubLam _ _ p)
         | inr r₁ =>
           match dec_eq C₁ C₂ with
           | Yes p =>
             match dec_eq A₁ (A₂ ⟶ A₂') with
             | Yes q =>
               match dec_eq
                       (transport (fun z => tm ar z _) p (transport (tm ar C₁) q t₁))
                       (λ f₂)
               with
               | Yes r => inl (EqSubTm _ _ p q r)
               | No r₂ => inr (not_subTerm_lam_3 r₁ r₂)
               end
             | No r₂ => inr (not_subTerm_lam_2 r₁ r₂)
             end
           | No r₂ => inr (not_subTerm_lam_1 r₁ r₂)
           end
         end           
       end.             

  (** * Properties of the subterm relation *)
  Definition subTm_trans
             {C₁ C₂ C₃ : con B}
             {A₁ A₂ A₃ : ty B}
             {t₁ : tm ar C₁ A₁}
             {t₂ : tm ar C₂ A₂}
             {t₃ : tm ar C₃ A₃}
             (H₁ : t₁ ≼ t₂)
             (H₂ : t₂ ≼ t₃)
    : t₁ ≼ t₃.
  Proof.
    revert C₁ A₁ t₁ H₁.
    induction H₂ as [ t₁ p
                    | ? ? ? ? ? H₂ IHH₂
                    | ? ? ? ? ? H₂ IHH₂
                    | ? ? ? ? H₂ IHH₂ ] ;
      intros C₁ A₁ t H₁.
    - subst.
      exact H₁.
    - apply SubAppL.
      apply IHH₂.
      exact H₁.
    - apply SubAppR.
      apply IHH₂.
      exact H₁.
    - apply SubLam.
      apply IHH₂.
      exact H₁.
  Defined.

  Fixpoint sub_subTerm
           {C₁ C₂ : con B}
           {A₁ A₂ : ty B}
           {t₁ : tm ar C₁ A₁}
           (t₁' : tm ar C₁ A₁)
           {t₂ : tm ar C₂ A₂}
           (H : t₁ ≼ t₂)
    : tm ar C₂ A₂
    := match H with
       | EqSubTm _ t₂ p q H => transport (fun z => tm ar z _) p (transport (tm _ _) q t₁')
       | SubAppL _ f₂ t₂ H => sub_subTerm t₁' H · t₂
       | SubAppR _ f₂ t₂ H => f₂ · sub_subTerm t₁' H
       | SubLam _ f₂ H => λ (sub_subTerm t₁' H)
       end.

  Definition subTerm_of_sub_subTerm
             {C₁ C₂ : con B}
             {A₁ A₂ : ty B}
             {t₁ : tm ar C₁ A₁}
             (t₁' : tm ar C₁ A₁)
             {t₂ : tm ar C₂ A₂}
             (H : t₁ ≼ t₂)
    : t₁' ≼ sub_subTerm t₁' H.
  Proof.
    induction H.
    - subst ; cbn.
      apply (EqSubTm _ _ (eq_refl _) (eq_refl _) (eq_refl _)).
    - cbn.
      apply SubAppL.
      assumption.
    - cbn.
      apply SubAppR.
      assumption.
    - cbn.
      apply SubLam.
      assumption.
  Defined.
End SubTerm.

Notation "t₁ ≼ t₂" := (subTerm t₁ t₂) (at level 50) : signature.

Import AFSNotation.

(** Rewriting in a subterm *)
Definition rew_subTerm
           {B F : Type}
           (X : afs B F)
           {C₁ C₂ : con B}
           {A₁ A₂ : ty B}
           {t₁ t₁' : tm X C₁ A₁}
           (r : t₁ ∼> t₁')
           {t₂ : tm X C₂ A₂}
           (H : t₁ ≼ t₂)
  : t₂ ∼> sub_subTerm t₁' H.
Proof.
  induction H as [ ? ? ? ? ?
                 | ? ? ? ? ? H IHH
                 | ? ? ? ? ? H IHH
                 | ? ? ? ? H IHH ].
  - subst ; cbn.
    exact r.
  - cbn.
    apply rew_App_l.
    exact IHH.
  - cbn.
    apply rew_App_r.
    exact IHH.
  - cbn.
    apply rew_Lam.
    exact IHH.
Defined.
