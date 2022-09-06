Require Import Prelude.Funext.
Require Import Prelude.WellfoundedRelation.
Require Import Prelude.CompatibleRelation.
Require Import Prelude.Lexico.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
Require Import Syntax.StrongNormalization.BetaReductionSN.
Require Import Interpretation.OrderInterpretation.
Require Import Interpretation.WeaklyMonotonicAlgebra.

Declare Scope poly_scope.

Inductive base_poly {B : Type} : con B -> Type :=
| P_const : forall {C : con B}, nat -> base_poly C
| P_plus : forall {C : con B}, base_poly C -> base_poly C -> base_poly C
| P_mult : forall {C : con B}, base_poly C -> base_poly C -> base_poly C
| from_poly : forall {C : con B} {b : B},
                poly C (Base b)
                -> base_poly C
with poly {B : Type} : con B -> ty B -> Type :=
| P_base : forall {C : con B} {b : B}, base_poly C -> poly C (Base b)
| P_var : forall {C : con B} {A : ty B},
            var C A
            -> poly C A
| P_app : forall {C : con B} {A₁ A₂ : ty B},
            poly C (A₁ ⟶ A₂)
            -> poly C A₁
            -> poly C A₂
| P_lam : forall {C : con B} {A₁ A₂ : ty B},
            poly (A₁ ,, C) A₂
            -> poly C (A₁ ⟶ A₂).

Notation "P1 +P P2" := (P_plus P1 P2) (at level 50) : poly_scope.
Notation "P1 *P P2" := (P_mult P1 P2) (at level 40) : poly_scope.
Notation "'λP' P" := (P_lam P) (at level 10) : poly_scope.
Notation "P1 ·P P2" := (P_app P1 P2) (at level 20) : poly_scope.

Fixpoint sem_base_poly
         {B : Type}
         {C : con B}
         (P : base_poly C)
  : weakMonotoneMap
      (sem_Con (fun _ => nat_CompatRel) C)
      nat_CompatRel
  := match P with
     | P_const n   => const_WM _ nat_CompatRel n
     | P_plus P1 P2  => plus_WM (sem_base_poly P1) (sem_base_poly P2)
     | P_mult P1 P2  => mult_WM (sem_base_poly P1) (sem_base_poly P2)
     | from_poly P   => sem_poly P
     end
with sem_poly
      {B : Type}
      {C : con B}
      {A : ty B}
      (P : poly C A)
  : weakMonotoneMap
      (sem_Con (fun _ => nat_CompatRel) C)
      (sem_Ty (fun _ => nat_CompatRel) A)
  := match P with 
     | P_base P   => sem_base_poly P
     | P_var v      => sem_Var (fun _ => nat_CompatRel) v
     | P_app P1 P2  => app_WM (sem_poly P1) (sem_poly P2)
     | P_lam P      => lambda_abs (sem_poly P)
     end.

Notation "⟦ P ⟧" := (sem_poly P).
Notation "⟦ P ⟧B" := (sem_base_poly P).

Definition prod_unit_map
           (A B : CompatRel)
  : weakMonotoneMap (A * B) (A * (B * unit_CompatRel)).
Proof.
  unshelve esplit.
  - exact (fun z => (fst z , (snd z , tt))).
  - intros z1 z2 p ; cbn.
    repeat split ; auto.
    + apply p.
    + apply p.
Defined.

Section PolyAlgebra.
  Context {B : Type} {F : Type}
          (X : afs B F)
          (P : forall (f : F), poly ∙ (arity X f))
          (app : forall (A1 A2 : ty B), poly ((A1 ⟶ A2) ,, A1 ,, ∙) A2).

  Definition p_base : B -> CompatRel
    := fun _ : B => nat_CompatRel.

  Definition p_tm (f : F) : sem_Ty p_base (arity X f)
    := sem_poly (P f) tt.

  Definition p_app (A1 A2 : ty B)
    := comp_WM
         (prod_unit_map
            (sem_Ty p_base (A1 ⟶ A2))
            (sem_Ty p_base A1))
         (sem_poly (app A1 A2)).
  
  Definition poly_WMalgebra
             (H1 : forall (A1 A2 : ty B)
                          (f : weakMonotoneMap (sem_Ty p_base A1) (sem_Ty p_base A2))
                          (x : sem_Ty p_base A1),
                 ⟦ app A1 A2 ⟧ (f , (x , tt)) >= f x)
             (H2 : forall (A1 A2 : ty B)
                          (f1 f2 : weakMonotoneMap (sem_Ty p_base A1) (sem_Ty p_base A2))
                          (x : sem_Ty p_base A1),
                 (forall z, f1 z > f2 z)
                 ->
                 ⟦ app A1 A2 ⟧ (f1, (x, tt))
                 >
                 ⟦ app A1 A2 ⟧ (f2 , (x , tt)))
             (H3 : forall (A1 A2 : ty B)
                          (f : weakMonotoneMap (sem_Ty p_base A1) (sem_Ty p_base A2))
                          (x1 x2 : sem_Ty p_base A1),
                 x1 > x2
                 ->
                 ⟦ app A1 A2 ⟧ (f , (x1 , tt))
                 >
                 ⟦ app A1 A2 ⟧ (f , (x2 , tt)))
             (H4 : forall (r : rewriteRules X)
                          (x : sem_Con p_base (vars r)),
                 sem_Tm p_base p_tm p_app (lhs r) x
                 >
                 sem_Tm p_base p_tm p_app (rhs r) x)
    : WMalgebra X.
  Proof.
    simple refine (make_WMalgebra
                     X
                     p_base
                     (fun _ => 0)
                     (fun _ => nat_Wf)
                     _
                     p_tm
                     p_app
                     H1 H2 H3 _).
    - intros r C s x.
      rewrite !sub_Lemma.
      apply H4.
  Defined.
End PolyAlgebra.


(*
Inductive base_poly {B : Type} : con B -> Type :=
| P_const : forall (C : con B), nat -> base_poly C
| P_plus : forall (C : con B), base_poly C -> base_poly C -> base_poly C
| P_mult : forall (C : con B), base_poly C -> base_poly C -> base_poly C
| P_b_app : forall (C : con B) (A : ty B) (b : B),
              poly C (A ⟶ Base b)
              -> poly C A
              -> base_poly C
| P_b_var : forall (C : con B) (b : B), var C (Base b) -> base_poly C
with poly {B : Type} : con B -> ty B -> Type :=
| P_base : forall (C : con B) (b : B), base_poly C -> poly C (Base b)
| P_var : forall (C : con B) (A : ty B),
            var C A
            -> poly C A
| P_app : forall (C : con B) (A₁ A₂ : ty B),
            poly C (A₁ ⟶ A₂)
            -> poly C A₁
            -> poly C A₂
| P_lam : forall (C : con B) (A₁ A₂ : ty B),
            poly (A₁ ,, C) A₂
            -> poly C (A₁ ⟶ A₂).
*)
(*
Inductive poly {B : Type} : con B -> ty B -> Type :=
| P_const : forall (C : con B) (b : B),
              nat -> poly C (Base b)
| P_plus : forall (C : con B) (b₁ b₂ b₃ : B),
              poly C (Base b₁)
              -> poly C (Base b₂)
              -> poly C (Base b₃)
| P_mult : forall (C : con B) (b₁ b₂ b₃ : B),
              poly C (Base b₁)
              -> poly C (Base b₂)
              -> poly C (Base b₃)
| P_var : forall (C : con B) (A : ty B),
            var C A
            -> poly C A
| P_app : forall (C : con B) (A₁ A₂ : ty B),
            poly C (A₁ ⟶ A₂)
            -> poly C A₁
            -> poly C A₂
| P_lam : forall (C : con B) (A₁ A₂ : ty B),
            poly (A₁ ,, C) A₂
            -> poly C (A₁ ⟶ A₂).


Definition sem_poly
         {B : Type}
         {C : con B}
         {A : ty B}
         (P : poly C A)
  : weakMonotoneMap
      (sem_Con (fun _ => nat_CompatRel) C)
      (sem_Ty (fun _ => nat_CompatRel) A).
Proof.
  induction P.
  - apply (const_WM _ nat_CompatRel n).
  - apply (plus_WM IHP1 IHP2).
  - apply (mult_WM IHP1 IHP2).
  - apply (sem_Var (fun _ => nat_CompatRel) v).
  - apply (app_WM IHP1 IHP2).
  - apply (lambda_abs IHP).
Defined.

(*
Inductive poly {B : Type} : con B -> ty B -> Type :=
| P_const   : forall (C : con B) (b : B),
                nat -> poly C (Base b)
| P_plus    : forall {C : con B} {b : B},
                poly C (Base b)
                -> poly C (Base b)
                -> poly C (Base b)
| P_mult    : forall {C : con B} {b : B},
                poly C (Base b)
                -> poly C (Base b)
                -> poly C (Base b)
| P_base    : forall {C : con B} {b : B},
                base_poly C (Base b)
                -> poly C (Base b)
| P_lam     : forall {C : con B} {A1 A2 : ty B},
                poly (A1 ,, C) A2
                -> poly C (A1 ⟶ A2)
with base_poly {B : Type} : con B -> ty B -> Type :=
| PVar      : forall {C : con B} {A : ty B},
                var C A
                -> base_poly C A
| Papp      : forall {C : con B} {A B : ty B},
                base_poly C (A ⟶ B)
                -> poly C A
                -> base_poly C B.

Fixpoint sem_poly
         {B : Type}
         {C : con B}
         {A : ty B}
         (P : poly C A)
  : weakMonotoneMap
      (sem_Con (fun _ => nat_CompatRel) C)
      (sem_Ty (fun _ => nat_CompatRel) A)
  := match P with
     | P_const _ _ n  => const_WM _ nat_CompatRel n
     | P_plus P1 P2   => plus_WM (sem_poly P1) (sem_poly P2)
     | P_mult P1 P2   => mult_WM (sem_poly P1) (sem_poly P2)
     | P_base P       => sem_base_poly P
     | P_lam P        => lambda_abs (sem_poly P)
     end
with sem_base_poly
     {B : Type}
     {C : con B}
     {A : ty B}
     (P : base_poly C A)
  : weakMonotoneMap
      (sem_Con (fun _ => nat_CompatRel) C)
      (sem_Ty (fun _ => nat_CompatRel) A)
  := match P with
     | PVar v         => sem_Var (fun _ => nat_CompatRel) v
     | Papp P1 P2     => app_WM (sem_base_poly P1) (sem_poly P2)
     end.

Definition prod_unit_map
           (A B : CompatRel)
  : weakMonotoneMap (A * B) (A * (B * unit_CompatRel)).
Proof.
  unshelve esplit.
  - exact (fun z => (fst z , (snd z , tt))).
  - intros z1 z2 p ; cbn.
    repeat split ; auto.
    + apply p.
    + apply p.
Defined.
  
Definition poly_WMalgebra
           {B : Type} {F : Type}
           (X : afs B F)
           (P : forall (f : F), poly ∙ (arity X f))
           (app : forall (A1 A2 : ty B), poly ((A1 ⟶ A2) ,, A1 ,, ∙) A2)
           (H1 : forall (A1 A2 : ty B)
                        (f : weakMonotoneMap
                               (sem_Ty (fun _ : B => nat_CompatRel) A1)
                               (sem_Ty (fun _ : B => nat_CompatRel) A2))
                        (x : sem_Ty (fun _ : B => nat_CompatRel) A1),
               sem_poly (app A1 A2) (f, (x, tt)) >= f x)
           (H2 : forall (A1 A2 : ty B)
                        (f1 f2 : weakMonotoneMap
                                   (sem_Ty (fun _ : B => nat_CompatRel) A1)
                                   (sem_Ty (fun _ : B => nat_CompatRel) A2))
                        (x : sem_Ty (fun _ : B => nat_CompatRel) A1),
               (forall z, f1 z > f2 z)
               ->
               sem_poly (app A1 A2) (f1, (x, tt))
               >
               sem_poly (app A1 A2) (f2 , (x , tt)))
           (H3 : forall (A1 A2 : ty B)
                        (f : weakMonotoneMap
                               (sem_Ty (fun _ : B => nat_CompatRel) A1)
                               (sem_Ty (fun _ : B => nat_CompatRel) A2))
                        (x1 x2 : sem_Ty (fun _ : B => nat_CompatRel) A1),
               x1 > x2
               ->
               sem_poly (app A1 A2) (f, (x1, tt))
               >
               sem_poly (app A1 A2) (f, (x2, tt)))
           (H4 : forall (r : rewriteRules X)
                        (x : sem_Con (fun _ : B => nat_CompatRel) (vars r)),
               sem_Tm
                 (fun _ : B => nat_CompatRel)
                 (fun f : F => sem_poly (P f) tt)
                 (fun A1 A2 : ty B =>
                    comp_WM
                      (prod_unit_map
                         (sem_Ty (fun _ : B => nat_CompatRel) (A1 ⟶ A2))
                         (sem_Ty (fun _ : B => nat_CompatRel) A1))
                      (sem_poly (app A1 A2)))
                 (lhs r)
                 x
               >
               sem_Tm
                 (fun _ : B => nat_CompatRel)
                 (fun f : F => sem_poly (P f) tt)
                 (fun A1 A2 : ty B =>
                    comp_WM
                      (prod_unit_map
                         (sem_Ty (fun _ : B => nat_CompatRel) (A1 ⟶ A2))
                         (sem_Ty (fun _ : B => nat_CompatRel) A1))
                      (sem_poly (app A1 A2)))
                 (rhs r)
                 x)
  : WMalgebra X.
Proof.
  simple refine (make_WMalgebra
                   X
                   (fun _ => nat_CompatRel)
                   (fun _ => 0)
                   (fun _ => nat_Wf)
                   _
                   (fun f => sem_poly (P f) tt)
                   (fun A1 A2 => comp_WM (prod_unit_map _ _) (sem_poly (app A1 A2)))
                   H1 H2 H3 _).
  - intros r C s x.
    rewrite !sub_Lemma.
    apply H4.
Defined.
 *)
 *)
