Require Import Prelude.Basics.
Require Import Prelude.Orders.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.SN.
Require Import Interpretation.OrderInterpretation.

Require Import Lia.
            
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

Fixpoint sem_base_poly
         {B : Type}
         {C : con B}
         (P : base_poly C)
  : weakMonotoneMap
      (sem_Con (fun _ => nat_CompatRel) C)
      nat_CompatRel
  := match P with
     | P_const n     => const_WM _ nat_CompatRel n
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
     | P_base P     => sem_base_poly P
     | P_var v      => sem_Var (fun _ => nat_CompatRel) v
     | P_app P1 P2  => app_WM (sem_poly P1) (sem_poly P2)
     | P_lam P      => lambda_abs (sem_poly P)
     end.

Section PolyAlgebra.
  Context {B : Type} {F : Type}
          (X : afs B F)
          (J : forall (f : F), poly ∙ (arity X f)).

  Definition p_base : B -> CompatRel
    := fun (_ : B) => nat_CompatRel.

  Definition p_fun_sym (f : F) : sem_Ty p_base (arity X f)
    := sem_poly (J f) tt.
  
  Fixpoint minimal_element_sem_ty
           (A : ty B)
    : minimal_element (sem_Ty p_base A)
    := match A with
       | Base _ => nat_minimal_element
       | A1 ⟶ A2 => min_el_fun_space _ (minimal_element_sem_ty A2)
       end.

  Fixpoint lower_value_function
           (A : ty B)
    : sem_Ty p_base A ⇒ nat_CompatRel
    := match A with
       | Base _ => id_WM nat_CompatRel
       | A₁ ⟶ A₂ => apply_el_WM (lower_value_function A₂) (minimal_element_sem_ty A₁)
       end.

  Proposition lower_value_function_strict_monotonic
              {A : ty B}
              {x x' : sem_Ty p_base A}
              (p : x > x')
    : lower_value_function A x > lower_value_function A x'.
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - exact p.
    - apply IHA₂.
      apply p.
  Qed.
              
  Fixpoint plus_ty_nat
           (A : ty B)
    : sem_Ty p_base A * nat_CompatRel ⇒ sem_Ty p_base A
    := match A with
       | Base _ => plus_as_weakMonotoneMap
       | A₁ ⟶ A₂ =>
           lambda_abs
             (comp_WM
                (pair_WM
                   (app_WM
                      (comp_WM (snd_WM _ _) (fst_WM _ _))
                      (fst_WM _ _))
                   (comp_WM (snd_WM _ _) (snd_WM _ _)))
                (plus_ty_nat A₂))
       end.

  Proposition plus_ty_nat_strict_monotone
              {A : ty B}
              (x : sem_Ty p_base A)
              {y y' : nat_CompatRel}
              (p : y > y')
    : plus_ty_nat A (x , y) > plus_ty_nat A (x , y').
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - cbn in p.
      lia.
    - intros z.
      apply IHA₂.
  Qed.

  Fixpoint plus_ty
           (A : ty B)
    : sem_Ty p_base A * sem_Ty p_base A ⇒ sem_Ty p_base A
    := match A with
       | Base _ => plus_as_weakMonotoneMap
       | A₁ ⟶ A₂ =>
           lambda_abs
             (comp_WM
                (pair_WM
                   (app_WM
                      (comp_WM (snd_WM _ _) (fst_WM _ _))
                      (fst_WM _ _))
                   (app_WM
                      (comp_WM (snd_WM _ _) (snd_WM _ _))
                      (fst_WM _ _)))
                (plus_ty A₂))
       end.

  Proposition plus_ty_ge_right
              {A : ty B}
              (x y y' : sem_Ty p_base A)
              (p : y >= y')
    : plus_ty A (x , y) >= y'.
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - cbn in p.
      lia.
    - intros z.
      apply IHA₂.
      apply p.
  Qed.

  Proposition plus_ty_strict_weak_monotonic
              {A : ty B}
              {x x' y y' : sem_Ty p_base A}
              (p : x > x')
              (q : y >= y')
    : plus_ty A (x , y) > plus_ty A (x' , y').
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - cbn in p, q.
      lia.
    - intros z.
      apply IHA₂.
      + apply p.
      + apply q.
  Qed.

  Proposition plus_ty_strict_monotonic
              {A : ty B}
              {x x' y y' : sem_Ty p_base A}
              (p : x > x')
              (q : y > y')
    : plus_ty A (x , y) > plus_ty A (x' , y').
  Proof.
    apply plus_ty_strict_weak_monotonic.
    - exact p.
    - apply compat.
      exact q.
  Qed.
             
  Fixpoint sum_of_lower_value_function
           (A : ty B)
    : sem_Ty p_base A
    := match A with
       | Base _ => 0
       | A₁ ⟶ A₂ =>
           make_monotone
             (fun x => plus_ty_nat
                         A₂
                         (sum_of_lower_value_function _
                          ,
                          lower_value_function _ x))
             _
       end.
  
  Definition p_app_fun
             {A1 A2 : ty B}
    : sem_Ty p_base (A1 ⟶ A2) * sem_Ty p_base A1 -> sem_Ty p_base A2
    := fun z =>
         let f := fst z in
         let x := snd z in
         plus_ty
           _
           (plus_ty_nat
              _
              (sum_of_lower_value_function A2
               ,
               lower_value_function _ f + lower_value_function _ x)
            ,
            f x).

  Global Instance weakMonotone_p_app_fun
                  (A1 A2 : ty B)
    : @weakMonotone
        (sem_Ty p_base (A1 ⟶ A2) * sem_Ty p_base A1)
        (sem_Ty p_base A2)
        p_app_fun.
  Proof.
    intros x₁ x₂ p.
    unfold p_app_fun.
    apply map_ge.
    split.
    - cbn.
      apply map_ge.
      split.
      * apply ge_refl.
      * apply plus_ge.
        ** apply (lower_value_function A2).
           apply p.
        ** apply (lower_value_function A1).
           apply p.
    - cbn.
      cbn in p.
      destruct p as [ p1 p2 ].
      refine (ge_trans (p1 _) _).
      apply map_ge.
      apply p2.
  Qed.
  
  Definition p_app
             (A1 A2 : ty B)
    : sem_Ty p_base (A1 ⟶ A2) * sem_Ty p_base A1 ⇒ sem_Ty p_base A2
    := @make_monotone
         (sem_Ty p_base (A1 ⟶ A2) * sem_Ty p_base A1)
         (sem_Ty p_base A2)
         p_app_fun
         _.

  Proposition p_app_ge_id
              (A₁ A₂ : ty B)
              (f : sem_Ty p_base A₁ ⇒ sem_Ty p_base A₂)
              (x : sem_Ty p_base A₁)
    : p_app_fun (f , x) >= f x.
  Proof.
    unfold p_app_fun ; cbn.
    apply plus_ty_ge_right.
    apply ge_refl.
  Qed.

  Proposition p_app_strict_l
              (A₁ A₂ : ty B)
              (f₁ f₂ : sem_Ty p_base A₁ ⇒ sem_Ty p_base A₂)
              (x : sem_Ty p_base A₁)
              (p : f₁ > f₂)
    : p_app_fun (f₁ , x) > p_app_fun (f₂ , x).
  Proof.
    unfold p_app_fun ; cbn.
    apply plus_ty_strict_monotonic.
    - apply plus_ty_nat_strict_monotone.
      cbn.
      enough (lower_value_function A₂ (f₁ (minimal_element_sem_ty A₁))
              >
              lower_value_function A₂ (f₂ (minimal_element_sem_ty A₁)))
        as H.
      {
        cbn in H.
        nia.
      }
      apply lower_value_function_strict_monotonic.
      apply p.
    - apply p.
  Qed.

  Proposition p_app_strict_r
              (A₁ A₂ : ty B)
              (f : sem_Ty p_base A₁ ⇒ sem_Ty p_base A₂)
              (x₁ x₂ : sem_Ty p_base A₁)
              (p : x₁ > x₂)
    : p_app_fun (f , x₁) > p_app_fun (f , x₂).
  Proof.
    unfold p_app_fun ; cbn.
    apply plus_ty_strict_weak_monotonic.
    - apply plus_ty_nat_strict_monotone.
      enough (lower_value_function A₁ x₁
              >
              lower_value_function A₁ x₂)
        as H.
      {
        cbn ; cbn in H.
        nia.
      }
      apply lower_value_function_strict_monotonic.
      exact p.
    - apply map_ge.
      apply compat.
      exact p.
  Qed.

  Definition poly_WMalgebra_rewrite_rules
             (H : forall (r : rewriteRules X)
                         (x : sem_Con p_base (vars r)),
                  sem_Tm p_base p_fun_sym p_app (lhs r) x
                  >
                  sem_Tm p_base p_fun_sym p_app (rhs r) x)
             (r : rewriteRules X)
             (C : con B)
             (s : sub (arity X) C (vars r))
             (x : sem_Con p_base C)
    : sem_Tm p_base p_fun_sym p_app (subTm (lhs r) s) x
      >
      sem_Tm p_base p_fun_sym p_app (subTm (rhs r) s) x.
  Proof.
    rewrite !sub_Lemma.
    apply H.
  Qed.
  
  Definition poly_WMalgebra
             (H : forall (r : rewriteRules X)
                         (x : sem_Con p_base (vars r)),
                  sem_Tm p_base p_fun_sym p_app (lhs r) x
                  >
                  sem_Tm p_base p_fun_sym p_app (rhs r) x)
    : Interpretation X.
  Proof.
    simple refine (make_Interpretation
                     X
                     p_base
                     _
                     (fun _ => 0)
                     (fun _ => nat_Wf)
                     p_fun_sym
                     p_app
                     _
                     _
                     _
                     _).
    - exact p_app_strict_l.
    - exact p_app_strict_r.
    - exact p_app_ge_id.
    - exact (poly_WMalgebra_rewrite_rules H).
  Defined.
End PolyAlgebra.
