Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.Types.
Require Import Nijn.Syntax.Signature.Contexts.
Require Import Nijn.Syntax.Signature.Terms.
Require Import Nijn.Syntax.Signature.TermWeakenings.
Require Import Nijn.Syntax.Signature.TermSubstitutions.

(** * Rewriting systems *)

(** First, we look at certain closure properties and how to create relations closed under these. The first one, is compatibility closure, which says that you can rewrite under all type formers. *)
Inductive compatibilityClosure
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          (R : forall (C : con B) (A : ty B), tm ar C A -> tm ar C A -> Type)
          (C : con B)
  : forall (A : ty B), tm ar C A -> tm ar C A -> Type
  :=
| App_l : forall {A1 A2 : ty B}
                 {f1 f2 : tm ar C (A1 ⟶ A2)}
                 (x : tm ar C A1),
    compatibilityClosure R _ _ f1 f2
    -> compatibilityClosure R _ _ (f1 · x) (f2 · x)
| App_r : forall {A1 A2 : ty B}
                 (f : tm ar C (A1 ⟶ A2))
                 {x1 x2 : tm ar C A1},
    compatibilityClosure R _ _ x1 x2
    -> compatibilityClosure R _ _ (f · x1) (f · x2)
| CLam : forall {A1 A2 : ty B}
               {f1 f2 : tm ar (A1 ,, C) A2},
    compatibilityClosure R _ _ f1 f2
    -> compatibilityClosure R _ _ (λ f1) (λ f2)
| CStep : forall {A : ty B}
                 {t1 t2 : tm ar C A},
    R _ _ t1 t2 -> compatibilityClosure R _ _ t1 t2.

Arguments App_l {_ _ _ _ _ _ _ _ _} _ _.
Arguments App_r {_ _ _ _ _ _ _} _ {_ _} _.
Arguments CLam {_ _ _ _ _ _ _ _ _} _.
Arguments CStep {_ _ _ _ _ _ _ _} _.

(** To formulate the beta rule, we need a particular substitution *)
Definition beta_sub
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : sub ar C (A ,, C)
  := ExtendSub (idSub C ar) t.

(** Reducing a beta redex *)
Inductive baseBetaStep
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          (C : con B)
  : forall (A : ty B), tm ar C A -> tm ar C A -> Type
  :=
| Beta : forall {A1 A2 : ty B}
                (f : tm ar (A1 ,, C) A2)
                (x : tm ar C A1),
    baseBetaStep _ _ ((λ f) · x) (subTm f (beta_sub x)).

Arguments Beta {_ _ _ _ _ _} _ _.

(** A single beta step *)
Definition betaStep
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
  : tm ar C A -> tm ar C A -> Type
  := compatibilityClosure baseBetaStep C A.

Notation "t1 '∼>β' t2" := (betaStep t1 t2) (at level 70). (* \sim is used *)

Definition betaRed
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
  : tm ar C A -> tm ar C A -> Type
  := transitiveClosure (fun t1 t2 => t1 ∼>β t2).

Notation "t1 '∼>β+' t2" := (betaRed t1 t2) (at level 70). (* \sim is used *)

(** Formers for beta reduction *)
Definition betaRed_step
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           {t1 t2 : tm ar C A}
           (p : t1 ∼>β t2)
  : t1 ∼>β+ t2
  := TStep p.

Definition beta_Trans
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           {t1 t2 t3 : tm ar C A}
           (p : t1 ∼>β+ t2)
           (q : t2 ∼>β+ t3)
  : t1 ∼>β+ t3
  := Trans p q.

Definition beta_rewrite_transport
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (p : A1 = A2)
           {x1 x2 : tm ar C A1}
           (r : x1 ∼>β x2)
  : transport (tm ar C) p x1 ∼>β transport (tm ar C) p x2
  := match p with
     | eq_refl => r
     end.

Definition beta_App_l_help
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 A3 : ty B}
           {f1 f2 : tm ar C A3}
           (x : tm ar C A1)
           (p : f1 ∼>β+ f2)
           (q : A3 = (A1 ⟶ A2))
  : ((transport (tm ar C) q f1) · x) ∼>β+ ((transport (tm ar C) q f2) · x).
Proof.
  induction p.
  - apply TStep.
    apply App_l.
    apply beta_rewrite_transport.
    exact r.
  - exact (Trans IHp1 IHp2).
Defined.

Definition beta_App_l
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           {f1 f2 : tm ar C (A1 ⟶ A2)}
           (x : tm ar C A1)
           (p : f1 ∼>β+ f2)
  : (f1 · x) ∼>β+ (f2 · x)
  := beta_App_l_help x p eq_refl.

Definition beta_App_r
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (f : tm ar C (A1 ⟶ A2))
           {x1 x2 : tm ar C A1}
           (p : x1 ∼>β+ x2)
  : (f · x1) ∼>β+ (f · x2).
Proof.
  induction p.
  - apply TStep.
    apply App_r.
    exact r.
  - exact (Trans IHp1 IHp2).
Defined.

Definition beta_Lam
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           {f1 f2 : tm ar (A1 ,, C) A2}
           (p : f1 ∼>β+ f2)
  : (λ f1) ∼>β+ (λ f2).
Proof.
  induction p.
  - apply TStep.
    apply CLam.
    exact r.
  - exact (Trans IHp1 IHp2).
Defined.

Definition beta_betaRed
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (f : tm ar (A1 ,, C) A2)
           (x : tm ar C A1)
  : ((λ f) · x) ∼>β+ (subTm f (beta_sub x)).
Proof.
  apply TStep.
  apply CStep.
  apply Beta.
Defined.

(** ** Any number of beta rewriting steps *)
Definition betaRed_nonneg
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
  : tm ar C A -> tm ar C A -> Type
  := reflexiveClosure (fun t1 t2 => t1 ∼>β+ t2).

Notation "t1 '∼>β*' t2" := (betaRed_nonneg t1 t2) (at level 70). (* \sim is used *)

Definition betaRed_nonneg_refl
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : t ∼>β* t.
Proof.
  right.
  reflexivity.
Defined.

Definition betaRed_nonneg_step
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           {t1 t2 : tm ar C A}
           (p : t1 ∼>β t2)
  : t1 ∼>β* t2.
Proof.
  left.
  apply betaRed_step.
  exact p.
Qed.

Definition betaRed_nonneg_steps
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           {t1 t2 : tm ar C A}
           (p : t1 ∼>β+ t2)
  : t1 ∼>β* t2.
Proof.
  left.
  exact p.
Qed.

Definition beta_nonneg_Trans
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           {t1 t2 t3 : tm ar C A}
           (p : t1 ∼>β* t2)
           (q : t2 ∼>β* t3)
  : t1 ∼>β* t3.
Proof.
  destruct p as [r1 | p], q as [r2 | q].
  - left.
    exact (beta_Trans r1 r2).
  - subst.
    left.
    exact r1.
  - subst.
    left.
    exact r2.
  - subst.
    right.
    reflexivity.
Defined.

Definition beta_nonneg_App_l
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           {f1 f2 : tm ar C (A1 ⟶ A2)}
           (x : tm ar C A1)
           (p : f1 ∼>β* f2)
  : (f1 · x) ∼>β* (f2 · x).
Proof.
  destruct p as [r | p].
  - left.
    apply beta_App_l.
    exact r.
  - subst.
    right.
    reflexivity.
Defined.

Definition beta_nonneg_App_r
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (f : tm ar C (A1 ⟶ A2))
           {x1 x2 : tm ar C A1}
           (p : x1 ∼>β* x2)
  : (f · x1) ∼>β* (f · x2).
Proof.
  destruct p as [r | p].
  - left.
    apply beta_App_r.
    exact r.
  - subst.
    right.
    reflexivity.
Defined.

Definition beta_nonneg_Lam
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           {f1 f2 : tm ar (A1 ,, C) A2}
           (p : f1 ∼>β* f2)
  : (λ f1) ∼>β* (λ f2).
Proof.
  destruct p as [r | p].
  - left.
    apply beta_Lam.
    exact r.
  - subst.
    right.
    reflexivity.
Defined.

Definition beta_nonneg_betaRed
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (f : tm ar (A1 ,, C) A2)
           (x : tm ar C A1)
  : ((λ f) · x) ∼>β* (subTm f (beta_sub x)).
Proof.
  left.
  apply beta_betaRed.
Defined.

(** * Rewriting relation for an AFS *)

(** An algebraic functional system is given by a type of base types, a type of function symbols, an arity for every function symbols, and a collection of rewrite rules. Given such data, we can define the rewrite relation. *)

(** First we look at the base steps in an AFS *)
Inductive baseRewStep
          {B : Type}
          {F : Type}
          {ar : F -> ty B}
          {R : Type}
          {Rcon : R -> con B}
          {Rtar : R -> ty B}
          (lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r))
          (C : con B)
  : forall (A : ty B), tm ar C A -> tm ar C A -> Type
  :=
| AFSBeta : forall {A : ty B}
                   (t1 t2 : tm ar C A),
    baseBetaStep _ _ t1 t2 -> baseRewStep lhs rhs _ _ t1 t2
| AFSRew : forall (r : R)
                  (s : sub ar C (Rcon r)),
    baseRewStep lhs rhs _ _ (lhs r [ s ]) (rhs r [ s ]).

Arguments AFSBeta {_ _ _ _ _ _} _ _ {_ _ _ _} _.
Arguments AFSRew {_ _ _ _ _ _} _ _ {_} _ _.

(** Now we introduce the single step relation *)
Definition rewStep
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           (lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r))
           {C : con B}
           {A : ty B}
  : tm ar C A -> tm ar C A -> Type
  := compatibilityClosure (baseRewStep lhs rhs) C A.

(** The rewriting relation in an AFS *)
Definition rew
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           (lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r))
           {C : con B}
           {A : ty B}
  : tm ar C A -> tm ar C A -> Type
  := transitiveClosure (fun t1 t2 => rewStep lhs rhs t1 t2).

(** Formers for reduction in an AFS *)
Definition rew_step
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           (lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r))
           {C : con B}
           {A : ty B}
           {t1 t2 : tm ar C A}
           (p : rewStep lhs rhs t1 t2)
  : rew lhs rhs t1 t2
  := TStep p.

Definition rew_Trans
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           {lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r)}
           {C : con B}
           {A : ty B}
           {t1 t2 t3 : tm ar C A}
           (p : rew lhs rhs t1 t2)
           (q : rew lhs rhs t2 t3)
  : rew lhs rhs t1 t3
  := Trans p q.

Definition rewrite_transport
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           {lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r)}
           {C : con B}
           {A1 A2 : ty B}
           (p : A1 = A2)
           {x1 x2 : tm ar C A1}
           (r : rewStep lhs rhs x1 x2)
  : rewStep lhs rhs (transport (tm ar C) p x1) (transport (tm ar C) p x2)
  := match p with
     | eq_refl => r
     end.

Definition rew_App_l_help
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           {lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r)}
           {C : con B}
           {A1 A2 A3 : ty B}
           {f1 f2 : tm ar C A3}
           (x : tm ar C A1)
           (p : rew lhs rhs f1 f2)
           (q : A3 = (A1 ⟶ A2))
  : rew lhs rhs ((transport (tm ar C) q f1) · x) ((transport (tm ar C) q f2) · x).
Proof.
  induction p.
  - apply TStep.
    apply App_l.
    apply rewrite_transport.
    exact r.
  - exact (Trans IHp1 IHp2).
Defined.

Definition rew_App_l
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           {lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r)}
           {C : con B}
           {A1 A2 : ty B}
           {f1 f2 : tm ar C (A1 ⟶ A2)}
           (x : tm ar C A1)
           (p : rew lhs rhs f1 f2)
  : rew lhs rhs (f1 · x) (f2 · x)
  := rew_App_l_help x p eq_refl. 

Definition rew_App_r
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           {lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r)}
           {C : con B}
           {A1 A2 : ty B}
           {f : tm ar C (A1 ⟶ A2)}
           (x1 x2 : tm ar C A1)
           (p : rew lhs rhs x1 x2)
  : rew lhs rhs (f · x1) (f · x2).
Proof.
  induction p.
  - apply TStep.
    apply App_r.
    exact r.
  - exact (Trans IHp1 IHp2).
Defined.

Definition rew_Lam
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           (lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r))
           {C : con B}
           {A1 A2 : ty B}
           {f1 f2 : tm ar (A1 ,, C) A2}
           (p : rew lhs rhs f1 f2)
  : rew lhs rhs (λ f1) (λ f2).
Proof.
  induction p.
  - apply TStep.
    apply CLam.
    exact r.
  - exact (Trans IHp1 IHp2).
Defined.

Definition rew_betaRed
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           (lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r))
           {C : con B}
           {A1 A2 : ty B}
           (f : tm ar (A1 ,, C) A2)
           (x : tm ar C A1)
  : rew lhs rhs ((λ f) · x) (subTm f (beta_sub x)).
Proof.
  apply TStep.
  apply CStep.
  apply AFSBeta.
  apply Beta.
Defined.

Definition rew_baseStep
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {R : Type}
           {Rcon : R -> con B}
           {Rtar : R -> ty B}
           (lhs rhs : forall (r : R), tm ar (Rcon r) (Rtar r))
           {C : con B}
           (r : R)
           (s : sub ar C (Rcon r))
  : rew lhs rhs (subTm (lhs r) s) (subTm (rhs r) s).
Proof.
  apply TStep.
  apply CStep.
  apply AFSRew.
Defined.
