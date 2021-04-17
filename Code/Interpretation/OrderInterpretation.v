Require Import Prelude.Funext.
Require Import Prelude.Wellfounded.
Require Import Prelude.CompatibleRelation.
Require Import Prelude.Lexico.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
Require Import Coq.Program.Equality.

Record Interpretation {B F R : Type} (X : AFS B F R) :=
  {
    semTy : Ty B -> CompatRel ;
    semCon : Con B -> CompatRel ;
    semTm : forall {C : Con B} {A : Ty B},
        Tm (Arity X) C A -> semCon C -> semTy A ;
    semRew : forall (r : R)
                    (C : Con B)
                    (s : Sub (Arity X) C (Vars X r))
                    (x : semCon C),
        semTm (subTm (Lhs X r) s) x > semTm (subTm (Rhs X r) s) x ;
    semBeta : forall {C : Con B}
                     {A1 A2 : Ty B}
                     (f : Tm (Arity X) (A1,, C) A2)
                     (t : Tm (Arity X) C A1)
                     (x : semCon C),
        semTm ((λ f) · t) x >= semTm (subTm f (beta_sub t)) x ;
    compatAppL : forall {C : Con B}
                        {A1 A2 : Ty B}
                        {f1 f2 : Tm (Arity X) C (A1 ⟶ A2)}
                        (t : Tm (Arity X) C A1)
                        (x : semCon C),
        semTm f1 x > semTm f2 x -> semTm (f1 · t) x > semTm (f2 · t) x ;
    compatAppR : forall {C : Con B}
                        {A1 A2 : Ty B}
                        (f : Tm (Arity X) C (A1 ⟶ A2))
                        {t1 t2 : Tm (Arity X) C A1}
                        (x : semCon C),
        semTm t1 x > semTm t2 x -> semTm (f · t1) x > semTm (f · t2) x ;
    compatLam : forall {C : Con B}
                       {A1 A2 : Ty B}
                       (f1 f2 : Tm (Arity X) (A1 ,, C) A2),
        (forall (x : semCon (A1 ,, C)), semTm f1 x > semTm f2 x)
        ->
        forall (x : semCon C), semTm (λ f1) x > semTm (λ f2) x
  }.

Arguments semTy {_ _ _ _} _ _.
Arguments semCon {_ _ _ _} _ _.
Arguments semTm {_ _ _ _} _ {_ _} _ _.
Arguments semRew {_ _ _ _} _ {_} _ _.
Arguments semBeta {_ _ _ _} _ {_ _ _} _ _ _.

Definition isWf_interpretation
           {B F R : Type}
           {X : AFS B F R}
           (I : Interpretation X)
  : Prop
  := forall (b : B), Wf (fun (x y : semTy I (Base b)) => x > y).

Section OrderInterpretation.
  Context {B : Type}
          (semB : B -> CompatRel)
          `{forall (b : B), isCompatRel (semB b)}.

  Fixpoint sem_Ty
           (A : Ty B)
    : CompatRel
    := match A with
       | Base b => semB b
       | A1 ⟶ A2 => sem_Ty A1 ⇒ sem_Ty A2
       end.

  Global Instance sem_Ty_CompatRel
         (A : Ty B)
    : isCompatRel (sem_Ty A).
  Proof.
    induction A ; apply _.
  Qed.
    
  Fixpoint sem_Con
           (C : Con B)
    : CompatRel
    := match C with
       | ∙ => unit_CompatRel
       | A ,, C => sem_Ty A * sem_Con C
       end.

  Global Instance sem_Con_isCompatRel
         (C : Con B)
    : isCompatRel (sem_Con C).
  Proof.
    induction C ; apply _.
  Qed.

  Fixpoint sem_Var_map
           {C : Con B}
           {A : Ty B}
           (v : Var C A)
    : sem_Con C -> sem_Ty A
    := match v with
       | Vz => fst
       | Vs v => fun x => sem_Var_map v (snd x)
       end.

  Global Instance sem_Var_strictMonotone
         {C : Con B}
         {A : Ty B}
         (v : Var C A)
    : strictMonotone (sem_Var_map v).
  Proof.
    induction v ; apply _.
  Qed.

  Global Instance sem_Var_weakMonotone
         {C : Con B}
         {A : Ty B}
         (v : Var C A)
    : weakMonotone (sem_Var_map v).
  Proof.
    induction v ; apply _.
  Qed.

  Definition sem_Var
             {C : Con B}
             {A : Ty B}
             (v : Var C A)
    : sem_Con C ⇒ sem_Ty A
    := make_monotone (sem_Var_map v) _.

  Context {F : Type}
          {ar : F -> Ty B}
          (semF : forall (f : F), sem_Ty (ar f))
          (semApp : forall (A1 A2 : Ty B),
              weakMonotoneMap ((sem_Ty A1 ⇒ sem_Ty A2) * sem_Ty A1) (sem_Ty A2)).

  Definition sem_Tm
             {C : Con B}
             {A : Ty B}
             (t : Tm ar C A)
    : weakMonotoneMap (sem_Con C) (sem_Ty A).
  Proof.
    induction t as [ ? f | ? ? v | ? ? ? ? IHf | ? ? ? f IHf t IHt ].
    - exact (const_WM _ _ (semF f)).
    - exact (sem_Var v).
    - exact (lambda_abs IHf).      
    - exact (comp_WM (pair_WM IHf IHt) (semApp A1 A2)).
  Defined.
End OrderInterpretation.

Definition sem_Wk
           {B : Type}
           (semB : B -> CompatRel)
           `{forall (b : B), isCompatRel (semB b)}
           {C1 C2 : Con B}
           (w : Wk C1 C2)
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
       {C1 C2 : Con B}
       (w : Wk C1 C2)
  : weakMonotone (sem_Wk semB w).
Proof.
  induction w ; apply _.
Qed.

Definition sem_Sub
           {B : Type}
           (semB : B -> CompatRel)
           `{forall (b : B), isCompatRel (semB b)}
           {F : Type}
           {ar : F -> Ty B}
           (semF : forall (f : F), sem_Ty semB (ar f))
           (semApp : forall (A1 A2 : Ty B),
               weakMonotoneMap
                 ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                 (sem_Ty semB A2))
           {C1 C2 : Con B}
           (s : Sub ar C1 C2)
  : sem_Con semB C1 -> sem_Con semB C2.
Proof.
  induction s as [ | ? ? ? ? s IHs t ].
  - exact (fun _ => tt).
  - exact (fun x => (sem_Tm semB semF semApp t x , IHs semF x)).
Defined.

Global Instance sem_Sub_weakMonotone
       {B : Type}
       (semB : B -> CompatRel)
       `{forall (b : B), isCompatRel (semB b)}
       {F : Type}
       {ar : F -> Ty B}
       (semF : forall (f : F), sem_Ty semB (ar f))
       (semApp : forall (A1 A2 : Ty B),
           weakMonotoneMap
             ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
             (sem_Ty semB A2))
       {C1 C2 : Con B}
       (s : Sub ar C1 C2)
  : weakMonotone (sem_Sub semB semF semApp s).
Proof.
  induction s ; apply _.
Qed.

Global Instance sem_Wk_strictMonotone
       {B : Type}
       (semB : B -> CompatRel)
       `{forall (b : B), isCompatRel (semB b)}
       {C1 C2 : Con B}
       (w : Wk C1 C2)
  : strictMonotone (sem_Wk semB w).
Proof.
  induction w.
  - intro ; cbn in *.
    contradiction.
  - apply _.
  - apply _.
Qed.

Proposition sem_idWk
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {C : Con B}
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
            {ar : F -> Ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : Ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            {C1 C2 : Con B}
            (w : Wk C1 C2)
            {A : Ty B}
            (v : Var C2 A)
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
            {ar : F -> Ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : Ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            {C1 C2 : Con B}
            (w : Wk C1 C2)
            {A1 A2 : Ty B}
            (t : Tm ar (A1 ,, C2) A2)
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
            {ar : F -> Ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : Ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            {C : Con B}
            {A1 A2 : Ty B}
            (t : Tm ar C A1)
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
            {ar : F -> Ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : Ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            {C1 C2 : Con B}
            (s : Sub ar C1 C2)
            {A : Ty B}
            (y : sem_Ty semB A)
            (x : sem_Con semB C1)
  : sem_Sub semB semF semApp (dropSub _ s) (y , x)
    =
    sem_Sub semB semF semApp s x.
Proof.
  induction s.
  - reflexivity.
  - simpl.
    rewrite (IHs semF).
    repeat f_equal.
    exact (sem_dropIdWk _ _ _ t x y).
Qed.

Proposition sem_idSub
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> Ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : Ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            {C : Con B}
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

Proposition sub_Lemma
            {B : Type}
            (semB : B -> CompatRel)
            `{forall (b : B), isCompatRel (semB b)}
            {F : Type}
            {ar : F -> Ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : Ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            {C1 C2 : Con B}
            (s : Sub ar C1 C2)
            {A : Ty B}
            (t : Tm ar C2 A)
            (x : sem_Con semB C1)
  : sem_Tm semB semF semApp (subTm t s) x
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
            {ar : F -> Ty B}
            (semF : forall (f : F), sem_Ty semB (ar f))
            (semApp : forall (A1 A2 : Ty B),
                weakMonotoneMap
                  ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                  (sem_Ty semB A2))
            (semApp_gt_id : forall (A1 A2 : Ty B)
                                   (f : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                                   (x : sem_Ty semB A1),
                semApp _ _ (f , x) >= f x)
            {C : Con B}
            {A1 A2 : Ty B}
            (f : Tm ar (A1 ,, C) A2)
            (t : Tm ar C A1)
            (x : sem_Con semB C)
  : sem_Tm
      semB semF semApp
      ((λ f) · t)
      x
    >=
    sem_Tm
      semB semF semApp
      (subTm f (beta_sub t))
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

Definition interpretation_to_lexico
           {B : Type}
           {semB : B -> CompatRel}
           `{forall (b : B), isCompatRel (semB b)}
           {F : Type}
           {ar : F -> Ty B}
           (semF : forall (f : F), sem_Ty semB (ar f))
           (semApp : forall (A1 A2 : Ty B),
               weakMonotoneMap
                 ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
                 (sem_Ty semB A2))
           {C : Con B}
           {A : Ty B}
           (x : Tm ar C A)
  : (sem_Con semB C ⇒ sem_Ty semB A) * Tm ar C A
  := (sem_Tm semB semF semApp x , x).

Definition sem_Rewrite
           {B : Type}
           (semB : B -> CompatRel)
           `{forall (b : B), isCompatRel (semB b)}
           {F : Type}
           {ar : F -> Ty B}
           (semF : forall (f : F), sem_Ty semB (ar f))
           (semApp : forall (A1 A2 : Ty B),
               weakMonotoneMap
              ((sem_Ty semB A1 ⇒ sem_Ty semB A2) * sem_Ty semB A1)
              (sem_Ty semB A2))
           (sem_App_l : forall (A1 A2 : Ty B)
                               (f1 f2 : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                               (x : sem_Ty semB A1),
               f1 > f2 -> semApp _ _ (f1 , x) > semApp _ _ (f2 , x))
           (sem_App_r : forall (A1 A2 : Ty B)
                               (f : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                               (x1 x2 : sem_Ty semB A1),
               x1 > x2 -> semApp _ _ (f , x1) > semApp _ _ (f , x2))
           (semApp_gt_id : forall (A1 A2 : Ty B)
                                  (f : sem_Ty semB A1 ⇒ sem_Ty semB A2)
                                  (x : sem_Ty semB A1),
               semApp _ _ (f , x) >= f x)
           {R : Type}
           {Rcon : R -> Con B}
           {Rtar : R -> B}
           (lhs rhs : forall (r : R), Tm ar (Rcon r) (Base (Rtar r)))
           (semR : forall (r : R)
                          (C : Con B)
                          (s : Sub ar C (Rcon r))
                          (x : sem_Con semB C),
               sem_Tm semB semF semApp (subTm (lhs r) s) x
               >
               sem_Tm semB semF semApp (subTm (rhs r) s) x)
           {C : Con B}
           {A : Ty B}
           {t1 t2 : Tm ar C A}
           (p : Rew lhs rhs t1 t2)
  : lexico
      (sem_Con semB C ⇒ sem_Ty semB A)
      (fun s1 s2 => BetaRed s1 s2)
      (interpretation_to_lexico semF semApp t1)
      (interpretation_to_lexico semF semApp t2).
Proof.
  induction p.
  - (* Trans *)
    refine (lexico_trans _ _ _ _ _).
    + intros ? ? ? q1 q2.
      exact (BetaTrans q1 q2).
    + apply IHp1.
    + apply IHp2.
  - (* Rew_App_l *)
    destruct IHp as [IHp | [IHp1 IHp2]].
    + left ; simpl.
      intro y.
      apply sem_App_l.
      exact (IHp y).
    + simpl in IHp1, IHp2.
      right ; simpl.
      split.
      * intro.
        apply (semApp _ _).
        split.
        ** simpl.
           intro.
           apply IHp1.
        ** simpl.
           apply ge_refl.
      * apply BetaRew_App_l.
        exact IHp2.
  - (* Rew_App_r *)
    destruct IHp as [IHp | [IHp1 IHp2]].
    + left ; simpl.
      intro y.
      apply sem_App_r.
      exact (IHp y).
    + right ; simpl.
      simpl in IHp1, IHp2.
      split.
      * intro.
        apply (semApp _ _).
        split ; simpl.
        ** intro.
           apply ge_refl.
        ** apply IHp1.
      * apply BetaRew_App_r.
        exact IHp2.
  - (* Rew_Lam *)
    destruct IHp as [IHp | [IHp1 IHp2]].
    + left ; simpl ; simpl in IHp.
      intros x y.
      apply IHp.
    + right ; simpl.
      simpl in IHp1, IHp2.
      split.
      * intros.
        apply IHp1.
      * apply BetaRew_Lam.
        exact IHp2.
  - (* Beta *)
    right ; simpl.
    split.
    + intros.
      apply sem_beta.
      apply semApp_gt_id.
    + apply BetaBeta.
  - (* BaseRew *)
    left ; simpl.
    intro x.
    apply semR.
Qed.



Record AFSAlgebra {B F R : Type} (X : AFS B F R) :=
  {
    sem_baseTy : B -> CompatRel ;
    sem_baseTy_el : forall (b : B), sem_baseTy b ;
    sem_baseTyWf : forall (b : B), Wf (fun (x y : sem_baseTy b) => x > y) ;
    sem_baseTy_isCompatRel : forall (b : B), isCompatRel (sem_baseTy b) ;
    sem_baseTm : forall (f : F), sem_Ty sem_baseTy (Arity X f) ;
    sem_App : forall (A1 A2 : Ty B),
        weakMonotoneMap
          ((sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2) * sem_Ty sem_baseTy A1)
          (sem_Ty sem_baseTy A2) ;
    sem_App_gt_id : forall {A1 A2 : Ty B}
                           (f : sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2)
                           (x : sem_Ty sem_baseTy A1),
        sem_App _ _ (f , x) >= f x ;
    sem_App_l : forall (A1 A2 : Ty B)
                       (f1 f2 : sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2)
                       (x : sem_Ty sem_baseTy A1),
        f1 > f2 -> sem_App _ _ (f1 , x) > sem_App _ _ (f2 , x) ;    
    sem_App_r : forall (A1 A2 : Ty B)
                       (f : sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2)
                       (x1 x2 : sem_Ty sem_baseTy A1),
        x1 > x2 -> sem_App _ _ (f , x1) > sem_App _ _ (f , x2) ;    
    sem_Rew : forall (r : R)
                     (C : Con B)
                     (s : Sub (Arity X) C (Vars X r))
                     (x : sem_Con sem_baseTy C),
        sem_Tm sem_baseTy sem_baseTm sem_App (subTm (Lhs X r) s) x
        >
        sem_Tm sem_baseTy sem_baseTm sem_App (subTm (Rhs X r) s) x
  }.

Arguments sem_baseTy {_ _ _ _}.
Arguments sem_baseTy_el {_ _ _ _}.
Arguments sem_baseTyWf {_ _ _ _} _ _ _.
Arguments sem_baseTy_isCompatRel {_ _ _ _}.
Arguments sem_baseTm {_ _ _ _}.
Arguments sem_App {_ _ _ _}.
Arguments sem_App_gt_id {_ _ _ _} _ {_ _} _ _.
Arguments sem_Rew {_ _ _ _}.

Global Instance AFSAlgebra_isCompatRel
       {B F R : Type}
       {X : AFS B F R}
       (Xalg : AFSAlgebra X)
  : forall (b : B), isCompatRel (sem_baseTy Xalg b)
  := sem_baseTy_isCompatRel Xalg.

Proposition AFSAlgebra_beta
            {B F R : Type}
            {X : AFS B F R}
            (Xalg : AFSAlgebra X)
            {C : Con B}
            {A1 A2 : Ty B}
            (f : Tm (Arity X) (A1 ,, C) A2)
            (t : Tm (Arity X) C A1)
            (x : sem_Con (sem_baseTy Xalg) C)
  : sem_Tm
      (sem_baseTy Xalg) (sem_baseTm Xalg) (sem_App Xalg)
      ((λ f) · t)
      x
    >=
    sem_Tm
      (sem_baseTy Xalg) (sem_baseTm Xalg) (sem_App Xalg)
      (subTm f (beta_sub t))
      x.
Proof.
  apply sem_beta.
  intros.
  apply (sem_App_gt_id Xalg).
Qed.

Theorem AFSAlgebra_to_Interpretation
        {B F R : Type}
        {X : AFS B F R}
        (Xalg : AFSAlgebra X)
  : Interpretation X.
Proof.
  unshelve esplit.
  - apply sem_Ty.
    exact (sem_baseTy Xalg).
  - apply sem_Con.
    exact (sem_baseTy Xalg).
  - apply sem_Tm.
    + exact (sem_baseTy_isCompatRel Xalg).
    + exact (sem_baseTm Xalg).
    + exact (sem_App Xalg).
  - exact (sem_Rew Xalg).
  - simpl.
    apply AFSAlgebra_beta.
  - simpl.
    intros.
    apply sem_App_l.
    assumption.
  - simpl.
    intros.
    apply sem_App_r.
    exact H.
  - simpl.
    intros.
    apply H.
Defined.

Theorem AFSAlgebra_to_WfInterpretation
        {B F R : Type}
        {X : AFS B F R}
        (Xalg : AFSAlgebra X)
  : isWf_interpretation (AFSAlgebra_to_Interpretation Xalg).
Proof.
  exact (sem_baseTyWf Xalg).
Defined.

Definition sem_Ty_el
           {B F R : Type}
           {X : AFS B F R}
           (Xalg : AFSAlgebra X)
           (A : Ty B)
  : sem_Ty (sem_baseTy Xalg) A.
Proof.
  induction A as [ b | A1 IHA1 A2 IHA2 ].
  - exact (sem_baseTy_el Xalg b).
  - simpl.
    apply const_WM.
    + apply sem_Ty_CompatRel.
      exact (sem_baseTy_isCompatRel Xalg).
    + exact IHA2.
Defined.

Definition sem_Con_el
           {B F R : Type}
           {X : AFS B F R}
           (Xalg : AFSAlgebra X)
           (C : Con B)
  : sem_Con (sem_baseTy Xalg) C.
Proof.
  induction C as [ | A C IHC ].
  - exact tt.
  - exact (sem_Ty_el Xalg A , IHC).
Defined.

Import AFSNotation.

Definition sem_Rew_AFS_Alg
           {B F R : Type}
           (b : B)
           {X : AFS B F R}
           (Xalg : AFSAlgebra X)
           {C : Con B}
           {A : Ty B}
           (t1 t2 : Tm X C A)
           (p : Rew X t1 t2)
  : lexico
      (sem_Con _ C ⇒ sem_Ty _ A)
      (fun s1 s2 => BetaRed _ s1 s2)
      (interpretation_to_lexico
         (sem_baseTm Xalg) (sem_App Xalg)
         t1)
      (interpretation_to_lexico
         (sem_baseTm Xalg) (sem_App Xalg)
         t2).
Proof.
  refine (sem_Rewrite _ _ _ _ _ _ _ _ _ p)
  ; apply Xalg.
Defined.

Theorem AFS_is_SN_from_Alg
        {B F R : Type}
        (b : B)
        {X : AFS B F R}
        (Xalg : AFSAlgebra X)
  : isSN X.
Proof.
  apply (SN_if_TySN X (Base b)).
  intro C.
  refine (fiber_is_Wf _ _ (sem_Rew_AFS_Alg b Xalg)).
  apply lexico_Wf.
  - apply _.
  - apply fun_Wf.
    + apply sem_Con_el.
    + apply Xalg.
  - admit.
Admitted.
