Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Nijn.TerminationTechniques.RuleRemoval.RuleSelector.
Require Import Coq.Program.Equality.

(** * Interpretations of algebraic functional systems  *)
Section OrderInterpretation.
  Context {B : Type}
          (semB : B -> CompatRel)
          `{forall (b : B), isCompatRel (semB b)}.

  (** ** Interpretation of types *)
  Fixpoint sem_Ty
           (A : ty B)
    : CompatRel
    := match A with
       | Base b   => semB b
       | A1 ⟶ A2  => sem_Ty A1 →wm sem_Ty A2
       end.

  Global Instance sem_Ty_CompatRel
         (A : ty B)
    : isCompatRel (sem_Ty A).
  Proof.
    induction A ; apply _.
  Qed.

  Fixpoint sem_Ty_el
           (els : forall (b : B), semB b)
           (A : ty B)
    : sem_Ty A
    := match A with
       | Base b    => (els b : sem_Ty (Base b))
       | A1 ⟶ A2  => const_wm (sem_Ty_el els A2)
       end.
  
  (** ** Interpretation of contexts *)  
  Fixpoint sem_Con
           (C : con B)
    : CompatRel
    := match C with
       | ∙       => unit_CompatRel
       | A ,, C  => sem_Ty A * sem_Con C
       end.

  Global Instance sem_Con_isCompatRel
         (C : con B)
    : isCompatRel (sem_Con C).
  Proof.
    induction C ; apply _.
  Qed.

  Fixpoint sem_Con_el
             (els : forall (b : B), semB b)
             (C : con B)
    : sem_Con C
    := match C with
       | ∙ => tt
       | A ,, C => (sem_Ty_el els A , sem_Con_el els C)
       end.

  (** ** Interpretation of variables *)
  Fixpoint sem_Var
           {C : con B}
           {A : ty B}
           (v : var C A)
    : sem_Con C →wm sem_Ty A
    := match v with
       | Vz => fst_wm
       | Vs v => sem_Var v ∘wm snd_wm
       end.

  Global Instance sem_Var_strictMonotone
         {C : con B}
         {A : ty B}
         (v : var C A)
    : strictMonotone (sem_Var v).
  Proof.
    induction v ; apply _.
  Qed.

  Context {F : Type}
          {ar : F -> ty B}
          (semF : forall (f : F), sem_Ty (ar f))
          (semApp : forall (A1 A2 : ty B),
                      (sem_Ty A1 →wm sem_Ty A2) * sem_Ty A1 →wm sem_Ty A2).

  (** ** Interpretation of terms *)
  Fixpoint sem_Tm
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
    : sem_Con C →wm sem_Ty A
    := match t with
       | BaseTm f  => const_wm (semF f)
       | TmVar v   => sem_Var v
       | λ f       => λwm (sem_Tm f)
       | f · t     => semApp _ _ ∘wm ⟨ sem_Tm f , sem_Tm t ⟩
       end.

  (** ** Interpretation of substitutions *)
  Fixpoint sem_Sub
           {C1 C2 : con B}
           (s : sub ar C1 C2)
    : sem_Con C1 →wm sem_Con C2
    := match s with
       | ToEmpty C  => const_wm (tt : unit_CompatRel)
       | s && t     => ⟨ sem_Tm t , sem_Sub s ⟩
       end.

  (** ** Interpretation of weakenings *)
  Definition sem_Wk
             {C1 C2 : con B}
             (w : wk C1 C2)
    : sem_Con C1 -> sem_Con C2.
  Proof.
    induction w as [ | ? ? ? w IHw | ? ? ? w IHw ].
    - exact (fun _ => tt).
    - exact (fun x => (fst x , IHw (snd x))).
    - exact (fun x => IHw (snd x)).
  Defined.

  Global Instance sem_Wk_weakMonotone
                  {C1 C2 : con B}
                  (w : wk C1 C2)
    : weakMonotone (sem_Wk w).
  Proof.
    induction w ; apply _.
  Qed.

  Global Instance sem_Wk_strictMonotone
                  {C1 C2 : con B}
                  (w : wk C1 C2)
    : strictMonotone (sem_Wk w).
  Proof.
    induction w.
    - intro ; cbn in *.
      contradiction.
    - apply _.
    - apply _.
  Qed.
End OrderInterpretation.

(** ** Lemmas on the interpretation of substitution *)
Proposition sem_idWk
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {C : con B}
            (x : sem_Con semB C)
  : sem_Wk semB (idWk C) x = x.
Proof.
  induction C as [ | A C IHC ].
  - destruct x.
    reflexivity.
  - destruct x ; simpl.
    rewrite IHC.
    reflexivity.
Qed.

Proposition sem_wkVar
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2)
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A : ty B}
            (v : var C2 A)
            (x : sem_Con semB C1)
  : sem_Tm semB semF semApp (TmVar (wkVar v w)) x
    =
    sem_Tm semB semF semApp (TmVar v) (sem_Wk semB w x).
Proof.
  induction w as [ | ? ? ? w IHw | ? ? ? w IHw ].
  - cbn.
    destruct x.
    reflexivity.
  - destruct x as [x1 x2].
    dependent induction v.
    + cbn.
      reflexivity.
    + simpl.
      apply IHw.
  - exact (IHw v (snd x)).
Qed.

Proposition sem_keepWk
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2)
            {C1 C2 : con B}
            (w : wk C1 C2)
            {A1 A2 : ty B}
            (t : tm ar (A1 ,, C2) A2)
            (x : sem_Con semB C1)
            (y : sem_Ty semB A1)
  : sem_Tm semB semF semApp (wkTm t (Keep A1 w)) (y , x)
    =
    sem_Tm semB semF semApp t (y , sem_Wk semB w x).
Proof.
  dependent induction t.
  - reflexivity.
  - dependent induction v.
    + reflexivity.
    + simpl.
      exact (sem_wkVar semB semF semApp w v x).
  - simpl.
    apply eq_weakMonotoneMap.
    intro a.
    simpl.
    refine (IHt semB _ semF semApp _ _ (Keep _ w) _ t _ _ _ _) ; auto.
  - simpl.
    do 2 f_equal.
    + apply IHt1 ; auto.
    + apply IHt2 ; auto.
Qed.

Proposition sem_dropIdWk
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2)
            {C : con B}
            {A1 A2 : ty B}
            (t : tm ar C A1)
            (x : sem_Con semB C)
            (y : sem_Ty semB A2)
  : sem_Tm semB semF semApp (wkTm t (Drop A2 (idWk C))) (y , x)
    =
    sem_Tm semB semF semApp t x.
Proof.
  dependent induction t.
  - reflexivity.
  - simpl.
    induction v.
    + reflexivity.
    + simpl.
      rewrite IHv.
      reflexivity.
  - simpl.
    apply eq_weakMonotoneMap.
    intro z ; simpl.
    rewrite (sem_keepWk _ _ _ (Drop A2 (idWk C)) t (y , x) z).
    do 2 f_equal.
    exact (sem_idWk _ x).
  - simpl.
    rewrite IHt1, IHt2.
    reflexivity.
Qed.

Proposition sem_dropSub
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2)
            {C1 C2 : con B}
            (s : sub ar C1 C2)
            {A : ty B}
            (y : sem_Ty semB A)
            (x : sem_Con semB C1)
  : sem_Sub semB semF semApp (dropSub _ s) (y , x)
    =
    sem_Sub semB semF semApp s x.
Proof.
  induction s.
  - reflexivity.
  - simpl.
    rewrite IHs.
    repeat f_equal.
    exact (sem_dropIdWk _ _ _ t x y).
Qed.

Proposition sem_idSub
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2)
            {C : con B}
            (x : sem_Con semB C)
  : x = sem_Sub semB semF semApp (idSub C ar) x.
Proof.
  induction C as [ | A C IHC ].
  - induction x ; cbn.
    reflexivity.
  - induction x as [x1 x2] ; simpl.
    f_equal.
    symmetry.
    etransitivity.
    {
      apply sem_dropSub.
    }
    symmetry.
    apply IHC.
Qed.

(** ** The substitution lemma *)
Proposition sub_Lemma
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2)
            {C1 C2 : con B}
            (s : sub ar C1 C2)
            {A : ty B}
            (t : tm ar C2 A)
            (x : sem_Con semB C1)
  : sem_Tm semB semF semApp (t [ s ]) x
    =
    sem_Tm semB semF semApp t (sem_Sub semB semF semApp s x).
Proof.
  revert s x.
  revert C1.
  induction t ; intros C1 s x.
  - reflexivity.
  - induction v.
    + dependent induction s.
      reflexivity.
    + dependent induction s.
      exact (IHv s).
  - simpl.
    apply eq_weakMonotoneMap.
    intro y.
    cbn.
    specialize (IHt _ (keepSub _ s) (y , x)).
    etransitivity.
    { 
      apply IHt.
    }
    simpl.
    do 2 f_equal.
    apply sem_dropSub.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

(** Interpretation of beta reduction *)
Proposition sem_beta
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2)
            (semApp_gt_id : forall (A1 A2 : ty B)
                                   (f : sem_Ty semB A1 →wm sem_Ty semB A2)
                                   (x : sem_Ty semB A1),
                semApp _ _ (f , x) >= f x)
            {C : con B}
            {A1 A2 : ty B}
            (f : tm ar (A1 ,, C) A2)
            (t : tm ar C A1)
            (x : sem_Con semB C)
  : sem_Tm
      semB semF semApp
      (λ f · t)
      x
    >=
    sem_Tm
      semB semF semApp
      (f [ beta_sub t ])
      x.
Proof.
  unfold beta_sub.
  rewrite sub_Lemma.
  simpl ; cbn.
  refine (ge_eq _ _).
  - apply semApp_gt_id.
  - simpl.
    do 2 f_equal.
    apply sem_idSub.
Qed.

(** * The notion of interpretation *)
Record InterpretationData {B F : Type} (X : afs B F) : Type :=
  make_InterpretationData
    {
      semB : B -> CompatRel ;
      semB_isCompatRel : forall (b : B), isCompatRel (semB b) ;
      els : forall (b : B), semB b ;
      semB_Wf : forall (b : B), Wf (fun (x y : semB b) => x > y) ;
      semF : forall (f : F), sem_Ty semB (arity X f) ;
      semApp : forall (A1 A2 : ty B),
                        (sem_Ty semB A1 →wm sem_Ty semB A2) * sem_Ty semB A1
                        →wm
                        sem_Ty semB A2 ;
      sem_App_l : forall (A1 A2 : ty B)
                         (f1 f2 : sem_Ty semB A1 →wm sem_Ty semB A2)
                         (x : sem_Ty semB A1),
        f1 > f2 -> semApp _ _ (f1 , x) > semApp _ _ (f2 , x) ;
      sem_App_r : forall (A1 A2 : ty B)
                         (f : sem_Ty semB A1 →wm sem_Ty semB A2)
                         (x1 x2 : sem_Ty semB A1),
        x1 > x2 -> semApp _ _ (f , x1) > semApp _ _ (f , x2) ;
      semApp_gt_id : forall (A1 A2 : ty B)
                            (f : sem_Ty semB A1 →wm sem_Ty semB A2)
                            (x : sem_Ty semB A1),
        semApp _ _ (f , x) >= f x
    }.

Arguments semB {B F X} _ _.
Arguments semF {B F X} _ _.
Arguments semApp {B F X} _ _.
Arguments els {B F X} _ _.
Arguments make_InterpretationData {_ _} _ _.

Global Instance interpretation_isCompatRel
                {B F : Type}
                {X : afs B F}
                (I : InterpretationData X)
                (b : B)
  : isCompatRel (semB I b).
Proof.
  apply semB_isCompatRel.
Defined.

Record Interpretation {B F : Type} (X : afs B F) : Type :=
  make_Interpretation
    {
      inter :> InterpretationData X ;
      semR : forall (r : rewriteRules X)
                    (C : con B)
                    (s : sub (arity X) C (vars r))
                    (x : sem_Con (semB inter) C),
        sem_Tm (semB _) (semF _) (semApp _) (lhs r [ s ]) x
        >
        sem_Tm (semB _) (semF _) (semApp _) (rhs r [ s ]) x
    }.

(** If we are using rule removal, then we need an interpretation that interprets some rule using the strict relation and other rules using the weaker one. The notion of [SelectorInterpretation] does this for us. *)
Record SelectorInterpretation
       {B F : Type}
       `{decEq B} `{decEq F}
       (X : afs B F)
       (P : selector X)
  : Type
  := make_SelectorInterpretation
       {
         s_inter :> InterpretationData X ;
         semR_gt : forall (r : rewriteRules X)
                          (C : con B)
                          (s : sub (arity X) C (vars r))
                          (x : sem_Con (semB s_inter) C),
                     selector_members P r
                     ->
                     sem_Tm (semB _) (semF _) (semApp _) (lhs r [ s ]) x
                     >
                     sem_Tm (semB _) (semF _) (semApp _) (rhs r [ s ]) x ;
         semR_ge : forall (r : rewriteRules X)
                          (C : con B)
                          (s : sub (arity X) C (vars r))
                          (x : sem_Con (semB s_inter) C),
                     ~(selector_members P r)
                     ->
                     sem_Tm (semB _) (semF _) (semApp _) (lhs r [ s ]) x
                     >=
                     sem_Tm (semB _) (semF _) (semApp _) (rhs r [ s ]) x
    }.

Definition sem_Ty_Wf
           {B F : Type}
           {X : afs B F}
           (I : InterpretationData X)
           (A : ty B)
  : @Wf (sem_Ty (semB I) A) (fun x y => x > y).
Proof.
  induction A as [ b | A₁ IHA₁ A₂ IHA₂ ].
  - apply semB_Wf.
  - cbn.
    apply fun_Wf.
    + apply sem_Ty_el.
      * apply _.
      * apply els.
    + apply IHA₂.
Defined.
  
(** * Strong normalization from interpretations *)
Definition interpretation_to_lexico
           {B F : Type}
           {X : afs B F}
           (I : Interpretation X)
           {C : con B}
           {A : ty B}
           (x : tm (arity X) C A)
  : (sem_Con (semB I) C →wm sem_Ty (semB I) A) * tm (arity X) C A
  := (sem_Tm (semB I) (semF I) (semApp I) x , x).

Import AFSNotation.

Definition sem_Rewrite_lexico
           {B F : Type}
           {X : afs B F}
           (I : Interpretation X)
           {C : con B}
           {A : ty B}
           (t1 t2 : tm X C A)
           (p : t1 ∼> t2)
  : lexico
      (sem_Con (semB I) C →wm sem_Ty (semB I) A)
      (fun s1 s2 => s1 ∼>β+ s2)
      (interpretation_to_lexico I t1)
      (interpretation_to_lexico I t2).
Proof.
  induction p.
  - induction r.
    + (* App_l *)
      destruct IHr as [IHr | [IHr1 IHr2]].
      * left ; simpl.
        intro y.
        apply sem_App_l.
        exact (IHr y).
      * simpl in IHr1, IHr2.
        right ; simpl.
        split.
        ** intro.
           apply (semApp _ _).
           split.
           *** simpl.
               intro.
               apply IHr1.
           *** simpl.
               apply ge_refl.
        ** apply beta_App_l.
           exact IHr2.
    + (* Rew_App_r *)
      destruct IHr as [IHr | [IHr1 IHr2]].
      * left ; simpl.
        intro y.
        apply sem_App_r.
        exact (IHr y).
      * right ; simpl.
        simpl in IHr1, IHr2.
        split.
        ** intro.
           apply (semApp _ _).
           split ; simpl.
           *** intro.
               apply ge_refl.
           *** apply IHr1.
        ** apply beta_App_r.
           exact IHr2.
    + (* Rew_Lam *)
      destruct IHr as [IHr | [IHr1 IHr2]].
      * left ; simpl ; simpl in IHr.
        intros x y.
        apply IHr.
      * right ; simpl.
        simpl in IHr1, IHr2.
        split.
        ** intros.
           apply IHr1.
        ** apply beta_Lam.
           exact IHr2.
    + induction r.
      * induction b.
        right ; simpl.
        split.
        ** intros.
           apply sem_beta.
           apply semApp_gt_id.
        ** apply beta_betaRed.
      * left ; simpl.
        intro.
        apply semR.
  - (* Trans *)
    refine (lexico_trans _ _ _ _ _).
    + intros ? ? ? q1 q2.
      exact (beta_Trans q1 q2).
    + apply IHp1.
    + apply IHp2.
Qed.

Theorem afs_is_SN_from_Interpretation
        {B F : Type}
        {X : afs B F}
        (I : Interpretation X)
  : isSN X.
Proof.
  intros C A.
  simple refine (fiber_Wf _ _ (sem_Rewrite_lexico I)).
  apply lexico_Wf.
  - apply _.
  - apply fun_Wf.
    + exact (sem_Con_el _ (els I) _).
    + induction A.
      * apply semB_Wf.
      * simpl.
        apply fun_Wf.
        ** exact (sem_Ty_el _ (els I) _).
        ** apply IHA2.
  - apply BetaRed_SN.
Qed.

(** ** Strong reduction pairs *)
Definition interpretation_to_term_order
           {B F : Type}
           {X : afs B F}
           (I : InterpretationData X)
  : term_order (arity X).
Proof.
  simple refine (make_term_order _ _ _).
  - intros C A t₁ t₂.
    exact (sem_Tm (semB I) (semF I) (semApp I) t₁
           >
           sem_Tm (semB I) (semF I) (semApp I) t₂).
  - intros C A t₁ t₂.
    exact (sem_Tm (semB I) (semF I) (semApp I) t₁
           >=
           sem_Tm (semB I) (semF I) (semApp I) t₂).
Defined.

Global Instance interpretation_to_term_isCompatRel
                {B F : Type}
                {X : afs B F}
                (I : InterpretationData X)
                (C : con B)
                (A : ty B)
  : isCompatRel (term_CompatRel (arity X) C A (interpretation_to_term_order I)).
Proof.
  unshelve esplit.
  - intros x y z p q w ; cbn in *.
    exact (gt_trans (p _) (q w)).
  - intros x y z p q w ; cbn in *.
    exact (ge_trans (p _) (q w)).
  - intros x w ; cbn in *.
    apply ge_refl.
  - intros x y p w.
    apply compat.
    apply p.
  - intros x y z p q w.
    apply (ge_gt (p w) (q w)).
  - intros x y z p q w.
    apply (gt_ge (p w) (q w)).
Qed.

Global Instance interpretation_is_strong_reduction_pair
                {B F : Type}
                {X : afs B F}
                (I : InterpretationData X)
  : is_strong_reduction_pair (arity X) (interpretation_to_term_order I).
Proof.
  unshelve esplit.
  - intros.
    cbn.
    simple refine (fiber_Wf _ _ _).
    + exact (sem_Con (semB I) C →wm sem_Ty (semB I) A).
    + exact (fun f g => f > g).
    + apply (fun_Wf
               (sem_Con (semB I) C)
               (sem_Ty (semB I) A) (sem_Con_el _ (els I) C)).
      apply sem_Ty_Wf.
    + exact (sem_Tm (semB I) (semF I) (semApp I)).
    + intros t₁ t₂ p x.
      exact (p x).
  - intros ; cbn ; apply _.
  - intros C₁ C₂ s A t₁ t₂ p x ; cbn.
    rewrite !sub_Lemma.
    apply p.
  - intros C₁ C₂ s A t₁ t₂ p x ; cbn.
    rewrite !sub_Lemma.
    apply p.
  - intros C A₁ A₂ f₁ f₂ t p x ; cbn.
    apply sem_App_l.
    apply p.
  - intros C A₁ A₂ f t₁ t₂ p x ; cbn.
    apply sem_App_r.
    apply p.
  - intros C A₁ A₂ f₁ f₂ t₁ t₂ p₁ p₂ x ; cbn.
    apply map_ge.
    split.
    + apply p₁.
    + apply p₂.
  - intros C A₁ A₂ f₁ f₂ p x y ; cbn.
    apply p.
  - intros C A₁ A₂ f₁ f₂ p x y ; cbn.
    apply p.
  - intros C A₁ A₂ f t x ; cbn.
    apply sem_beta.
    intros.
    apply semApp_gt_id.
Qed.

Definition interpretation_to_strong_reduction_pair
           {B F : Type}
           {X : afs B F}
           (I : InterpretationData X)
  : strong_reduction_pair (arity X)
  := make_srp _ (interpretation_to_term_order I) _.

Definition interpretation_respects_selector
           {B F : Type}
           `{decEq B}
           `{decEq F}
           {X : afs B F}
           (P : selector X)
           (I : SelectorInterpretation X P)
  : respects_selector X (interpretation_to_strong_reduction_pair I) P.
Proof.
  split.
  - intros r Hr x.
    pose (semR_gt X P I r (vars r) (idSub _ _) x Hr) as p.
    rewrite !subTm_id in p.
    exact p.
  - intros r Hr x.
    pose (semR_ge X P I r (vars r) (idSub _ _) x Hr) as p.
    rewrite !subTm_id in p.
    exact p.
Qed.
