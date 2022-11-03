Require Import Prelude.Funext.
Require Import Prelude.WellfoundedRelation.
Require Import Prelude.Orders.
Require Import Prelude.Lexico.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
Require Import Syntax.StrongNormalization.BetaReductionSN.
Require Import Coq.Program.Equality.

(** Below we discuss the lemmas which are needed to get an interpretation of an AFS *)
Section OrderInterpretation.
  Context {B : Type}
          (semB : B -> CompatRel)
          `{forall (b : B), isCompatRel (semB b)}.

  (** Interpretation of types *)
  Fixpoint sem_Ty
           (A : ty B)
    : CompatRel
    := match A with
       | Base b    => semB b
       | A1 ⟶ A2  => sem_Ty A1 ⇒ sem_Ty A2
       end.

  Global Instance sem_Ty_CompatRel
         (A : ty B)
    : isCompatRel (sem_Ty A).
  Proof.
    induction A ; apply _.
  Qed.
  
  (** Interpretation of contexts *)  
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

  Fixpoint sem_Var_map
           {C : con B}
           {A : ty B}
           (v : var C A)
    : sem_Con C -> sem_Ty A
    := match v with
       | Vz    => fst
       | Vs v  => fun x => sem_Var_map v (snd x)
       end.

  Global Instance sem_Var_strictMonotone
         {C : con B}
         {A : ty B}
         (v : var C A)
    : strictMonotone (sem_Var_map v).
  Proof.
    induction v ; apply _.
  Qed.

  Global Instance sem_Var_weakMonotone
         {C : con B}
         {A : ty B}
         (v : var C A)
    : weakMonotone (sem_Var_map v).
  Proof.
    induction v ; apply _.
  Qed.

  (** Interpretation of variables *)
  Definition sem_Var
             {C : con B}
             {A : ty B}
             (v : var C A)
    : sem_Con C ⇒ sem_Ty A
    := make_monotone (sem_Var_map v) _.

  Context {F : Type}
          {ar : F -> ty B}
          (semF : forall (f : F), sem_Ty (ar f))
          (semApp : forall (A1 A2 : ty B),
              (sem_Ty A1 ⇒ sem_Ty A2) * sem_Ty A1 ⇒ sem_Ty A2).

  (** Interpretation of terms *)
  Fixpoint sem_Tm
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
    : sem_Con C ⇒ sem_Ty A
    := match t with
       | BaseTm f  => const_WM _ _ (semF f)
       | TmVar v   => sem_Var v
       | λ f       => lambda_abs (sem_Tm f)
       | f · t     => comp_WM (pair_WM (sem_Tm f) (sem_Tm t)) (semApp _ _)
       end.
  
  Fixpoint sem_Sub
           {C1 C2 : con B}
           (s : sub ar C1 C2)
    : sem_Con C1 -> sem_Con C2
    := match s with
       | ToEmpty C => fun _ => tt
       | s && t => fun x => (sem_Tm t x , sem_Sub s x)
       end.

  Global Instance sem_Sub_weakMonotone
                  {C1 C2 : con B}
                  (s : sub ar C1 C2)
    : weakMonotone (sem_Sub s).
  Proof.
    induction s ; apply _.
  Qed.
End OrderInterpretation.

Definition sem_Ty_el
           {B : Type}
           (semB : B -> CompatRel)
           `{forall (b : B), isCompatRel (semB b)}
           (els : forall (b : B), semB b)
           (A : ty B)
  : sem_Ty semB A.
Proof.
  induction A as [ | A1 IHA1 A2 IHA2 ].
  - apply els.
  - exact (const_WM _ _ IHA2).
Defined.

Definition sem_Con_el
           {B : Type}
           (semB : B -> CompatRel)
           `{forall (b : B), isCompatRel (semB b)}           
           (els : forall (b : B), semB b)
           (C : con B)
  : sem_Con semB C.
Proof.
  induction C as [ | A C IHC ].
  - exact tt.
  - split.
    + apply sem_Ty_el.
      * apply _.
      * exact els.
    + apply IHC.
Defined.

(** Interpretation of weakenings *)
Definition sem_Wk
           {B : Type}
           (semB : B -> CompatRel)
           `{forall (b : B), isCompatRel (semB b)}
           {C1 C2 : con B}
           (w : wk C1 C2)
  : sem_Con semB C1 -> sem_Con semB C2.
Proof.
  induction w as [ | ? ? ? w IHw | ? ? ? w IHw ].
  - exact (fun _ => tt).
  - exact (fun x => (fst x , IHw (snd x))).
  - exact (fun x => IHw (snd x)).
Defined.

Global Instance sem_Wk_weakMonotone
       {B : Type}
       (semB : B -> CompatRel)
       `{forall (b : B), isCompatRel (semB b)}
       {C1 C2 : con B}
       (w : wk C1 C2)
  : weakMonotone (sem_Wk semB w).
Proof.
  induction w ; apply _.
Qed.

Global Instance sem_Wk_strictMonotone
       {B : Type}
       (semB : B -> CompatRel)
       `{forall (b : B), isCompatRel (semB b)}
       {C1 C2 : con B}
       (w : wk C1 C2)
  : strictMonotone (sem_Wk semB w).
Proof.
  induction w.
  - intro ; cbn in *.
    contradiction.
  - apply _.
  - apply _.
Qed.

(** Interpretation of substitutions *)
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
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
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
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
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
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
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
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
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
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            {C : con B}
            (x : sem_Con semB C)
  : x = sem_Sub semB semF semApp (idSub C ar) x.
Proof.
  induction C as [ | A C IHC ].
  - induction x ; cbn.
    reflexivity.
  - induction x as [x1 x2] ; simpl.
    f_equal.
    rewrite sem_dropSub.
    apply IHC.
Qed.

(** The substitution lemma *)
Proposition sub_Lemma
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
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
    rewrite sem_dropSub.
    reflexivity.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

Proposition sem_beta
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            (semApp_gt_id : forall (A1 A2 : ty B)
                                   (f : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                                   (x : sem_Ty semB A1),
                semApp _ _ (f , x) >= f x)
            {C : con B}
            {A1 A2 : ty B}
            (f : tm ar (A1 ,, C) A2)
            (t : tm ar C A1)
            (x : sem_Con semB C)
  : sem_Tm
      semB semF semApp
      ((λ f) · t)
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

Record Interpretation {B F : Type} (X : afs B F) : Type :=
  make_Interpretation
    {
      semB : B -> CompatRel ;
      semB_isCompatRel : forall (b : B), isCompatRel (semB b) ;
      els : forall (b : B), semB b ;
      semB_Wf : forall (b : B), Wf (fun (x y : semB b) => x > y) ;
      semF : forall (f : F), sem_Ty semB (arity X f) ;
      semApp : forall (A1 A2 : ty B),
        weakMonotoneMap
          ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
          (sem_Ty semB A2) ;
      sem_App_l : forall (A1 A2 : ty B)
                         (f1 f2 : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                         (x : sem_Ty semB A1),
        f1 > f2 -> semApp _ _ (f1 , x) > semApp _ _ (f2 , x) ;
      sem_App_r : forall (A1 A2 : ty B)
                         (f : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                         (x1 x2 : sem_Ty semB A1),
        x1 > x2 -> semApp _ _ (f , x1) > semApp _ _ (f , x2) ;
      semApp_gt_id : forall (A1 A2 : ty B)
                            (f : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                            (x : sem_Ty semB A1),
        semApp _ _ (f , x) >= f x ;
      semR : forall (r : rewriteRules X)
                    (C : con B)
                    (s : sub (arity X) C (vars r))
                    (x : sem_Con semB C),
        sem_Tm semB semF semApp (lhs r [ s ]) x
        >
        sem_Tm semB semF semApp (rhs r [ s ]) x
    }.

Arguments semB {B F X} _ _.
Arguments semF {B F X} _ _.
Arguments semApp {B F X} _ _.
Arguments els {B F X} _ _.
Arguments make_Interpretation {_ _} _ _.

Global Instance interpretation_isCompatRel
                {B F : Type}
                {X : afs B F}
                (I : Interpretation X)
                (b : B)
  : isCompatRel (semB I b).
Proof.
  apply semB_isCompatRel.
Defined.           

Definition interpretation_to_lexico
           {B F : Type}
           {X : afs B F}
           (I : Interpretation X)
           {C : con B}
           {A : ty B}
           (x : tm (arity X) C A)
  : (sem_Con (semB I) C ⇒ sem_Ty (semB I) A) * tm (arity X) C A
  := (sem_Tm (semB I) (semF I) (semApp I) x , x).

Import AFSNotation.

Definition sem_Rewrite_lexico
           {B F : Type}
           {X : afs B F}
           (I : Interpretation X)
           {C : con B}
           {A : ty B}
           (t1 t2 : tm X C A)
           (p : t1 ~> t2)
  : lexico
      (sem_Con (semB I) C ⇒ sem_Ty (semB I) A)
      (fun s1 s2 => s1 ~>β+ s2)
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
