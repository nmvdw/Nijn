Require Import Prelude.Funext.
Require Import Prelude.Wellfounded.
Require Import Prelude.CompatibleRelation.
Require Import Prelude.Lexico.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
(* Require Import Syntax.StrongNormalization.BetaReductionSN. *)
Require Import Interpretation.OrderInterpretation.
Require Import Coq.Program.Equality.

(** * Weakly monotonic algebras *)

(** We use weakly monotonic algebras to obtain interpretations. They consist of the following data. *)
Record WMalgebra {B F R : Type} (X : afs B F R) :=
  {
    sem_baseTy : B -> CompatRel ;
    sem_baseTy_el : forall (b : B), sem_baseTy b ;
    sem_baseTyWf : forall (b : B), Wf (fun (x y : sem_baseTy b) => x > y) ;
    sem_baseTy_isCompatRel : forall (b : B), isCompatRel (sem_baseTy b) ;
    sem_baseTm : forall (f : F), sem_Ty sem_baseTy (Arity X f) ;
    sem_App : forall (A1 A2 : ty B),
        weakMonotoneMap
          ((sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2) * sem_Ty sem_baseTy A1)
          (sem_Ty sem_baseTy A2) ;
    sem_App_gt_id : forall {A1 A2 : ty B}
                           (f : sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2)
                           (x : sem_Ty sem_baseTy A1),
        sem_App _ _ (f , x) >= f x ;
    sem_App_l : forall (A1 A2 : ty B)
                       (f1 f2 : sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2)
                       (x : sem_Ty sem_baseTy A1),
        f1 > f2 -> sem_App _ _ (f1 , x) > sem_App _ _ (f2 , x) ;    
    sem_App_r : forall (A1 A2 : ty B)
                       (f : sem_Ty sem_baseTy A1 ⇒ sem_Ty sem_baseTy A2)
                       (x1 x2 : sem_Ty sem_baseTy A1),
        x1 > x2 -> sem_App _ _ (f , x1) > sem_App _ _ (f , x2) ;    
    sem_Rew : forall (r : R)
                     (C : con B)
                     (s : sub (Arity X) C (Vars X r))
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

Global Instance afsAlgebra_isCompatRel
       {B F R : Type}
       {X : afs B F R}
       (Xalg : WMalgebra X)
  : forall (b : B), isCompatRel (sem_baseTy Xalg b)
  := sem_baseTy_isCompatRel Xalg.

Proposition afsAlgebra_beta
            {B F R : Type}
            {X : afs B F R}
            (Xalg : WMalgebra X)
            {C : con B}
            {A1 A2 : ty B}
            (f : tm (Arity X) (A1 ,, C) A2)
            (t : tm (Arity X) C A1)
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

(** Note that we obtain an interpretation if we have a weakly monotonic algebra *)
Theorem afsAlgebra_to_Interpretation
        {B F R : Type}
        {X : afs B F R}
        (Xalg : WMalgebra X)
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
    apply afsAlgebra_beta.
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

Theorem afsAlgebra_to_WfInterpretation
        {B F R : Type}
        {X : afs B F R}
        (Xalg : WMalgebra X)
  : isWf_interpretation (afsAlgebra_to_Interpretation Xalg).
Proof.
  exact (sem_baseTyWf Xalg).
Defined.

(** The following lemmas are needed to prove strong normalization *)
Definition sem_Ty_el
           {B F R : Type}
           {X : afs B F R}
           (Xalg : WMalgebra X)
           (A : ty B)
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
           {X : afs B F R}
           (Xalg : WMalgebra X)
           (C : con B)
  : sem_Con (sem_baseTy Xalg) C.
Proof.
  induction C as [ | A C IHC ].
  - exact tt.
  - exact (sem_Ty_el Xalg A , IHC).
Defined.

Import AFSNotation.

Definition sem_Rew_afs_Alg
           {B F R : Type}
           {X : afs B F R}
           (Xalg : WMalgebra X)
           {C : con B}
           {A : ty B}
           (t1 t2 : tm X C A)
           (p : rew X t1 t2)
  : lexico
      (sem_Con _ C ⇒ sem_Ty _ A)
      (fun s1 s2 => betaRed _ s1 s2)
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

Theorem afs_is_SN_from_Alg
        {B F R : Type}
        {X : afs B F R}
        (Xalg : WMalgebra X)
  : isSN X.
Proof.
  intros C A.
  refine (fiber_is_Wf _ _ (sem_Rew_afs_Alg Xalg)).
  apply lexico_Wf.
  - apply _.
  - apply fun_Wf.
    + apply sem_Con_el.
    + induction A.
      * simpl.
        apply Xalg.
      * simpl.
        apply fun_Wf.
        ** apply sem_Ty_el.
        ** apply IHA2.
  - admit. (* strong normaliation of the simply typed lambda calculus *)
Admitted.
