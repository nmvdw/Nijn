Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Nijn.Interpretation.OrderInterpretation.

Require Import Lia.

(** * The notation of polynomials *)
(** Note that we define both base polynomials and arbitrary polynomials and that we can convert between base polynomials and polynomials of a base type. Since base polynomials do not keep track of the type, we can freely add and multiply them without worrying about whether their types are actually the same. *)
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

(** * Polynomial interpretation *)
Section PolyAlgebra.
  Context {B : Type} {F : Type}
          (X : afs B F)
          (J : forall (f : F), poly ∙ (arity X f)).

  Definition p_base : B -> CompatRel
    := fun (_ : B) => nat_CompatRel.
  
  Notation "⟦ C ⟧con" := (sem_Con p_base C).
  Notation "⟦ A ⟧ty" := (sem_Ty p_base A).

  (** ** Semantics of polynomials *)
  Fixpoint sem_base_poly
           {C : con B}
           (P : base_poly C)
    : ⟦ C ⟧con →wm nat_CompatRel
    := match P with
       | P_const n     => const_wm (n : nat_CompatRel)
       | P_plus P1 P2  => plus_fun_wm (sem_base_poly P1) (sem_base_poly P2)
       | P_mult P1 P2  => mult_fun_wm (sem_base_poly P1) (sem_base_poly P2)
       | from_poly P   => sem_poly P
       end
   with sem_poly
        {C : con B}
        {A : ty B}
        (P : poly C A)
    : ⟦ C ⟧con →wm ⟦ A ⟧ty
    := match P with 
       | P_base P     => sem_base_poly P
       | P_var v      => sem_Var _ v
       | P_app P1 P2  => sem_poly P1 ·wm sem_poly P2
       | P_lam P      => λwm (sem_poly P)
       end.

  Notation "⟦ P ⟧poly" := (sem_poly P).

  Definition p_fun_sym (f : F) : ⟦ arity X f ⟧ty
    := ⟦ J f ⟧poly tt.

  (** ** Minimal element of types *)
  Fixpoint min_el_ty
           (A : ty B)
    : minimal_element ⟦ A ⟧ty
    := match A with
       | Base _ => nat_minimal_element
       | A1 ⟶ A2 => min_el_fun_space (min_el_ty A2)
       end.

  (** ** Lower value functions *)
  Fixpoint lvf
           {A : ty B}
    : ⟦ A ⟧ty →wm nat_CompatRel
    := match A with
       | Base _ => id_wm
       | A₁ ⟶ A₂ => lvf ∘wm apply_el_wm (min_el_ty A₁)
       end.

  Proposition lvf_strict_monotonic
              {A : ty B}
              {x x' : ⟦ A ⟧ty}
              (p : x > x')
    : lvf x > lvf x'.
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - exact p.
    - apply IHA₂.
      apply p.
  Qed.

  (** ** Addition with natural numbers *)
  Fixpoint plus_ty_nat
           {A : ty B}
    : ⟦ A ⟧ty * nat_CompatRel →wm ⟦ A ⟧ty
    := match A with
       | Base _ => plus_wm
       | A1 ⟶ A2 =>
           let f := fst_wm ∘wm snd_wm in
           let x := fst_wm in
           let n := snd_wm ∘wm snd_wm in
           λwm (plus_ty_nat ∘wm ⟨ f ·wm x , n ⟩)
       end.

  Notation "f '+c' n" := (plus_ty_nat (f , n)) (at level 50).

  Proposition plus_ty_nat_strict_monotone
              {A : ty B}
              (x : ⟦ A ⟧ty)
              {y y' : nat_CompatRel}
              (p : y > y')
    : x +c y > x +c y'.
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - cbn in p.
      lia.
    - intros z.
      apply IHA₂.
  Qed.

  (** ** Addition on the interpretation of types *)
  Fixpoint plus_ty
           {A : ty B}
    : ⟦ A ⟧ty * ⟦ A ⟧ty →wm ⟦ A ⟧ty
    := match A with
       | Base _ => plus_wm
       | A1 ⟶ A2 =>
           let f := fst_wm ∘wm snd_wm in
           let g := snd_wm ∘wm snd_wm in
           let x := fst_wm in
           λwm (plus_ty ∘wm ⟨ f ·wm x , g ·wm x ⟩)
       end.

  Notation "f '+f' g" := (plus_ty (f , g)) (at level 50).
  
  Proposition plus_ty_ge_right
              {A : ty B}
              (x y y' : ⟦ A ⟧ty)
              (p : y >= y')
    : x +f y >= y'.
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
              {x x' y y' : ⟦ A ⟧ty}
              (p : x > x')
              (q : y >= y')
    : x +f y > x' +f y'.
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
              {x x' y y' : ⟦ A ⟧ty}
              (p : x > x')
              (q : y > y')
    : x +f y > x' +f y'.
  Proof.
    apply plus_ty_strict_weak_monotonic.
    - exact p.
    - apply compat.
      exact q.
  Qed.

  (** ** Sum of the lower value functions *)
  Fixpoint sum_lvf
           (A : ty B)
    : ⟦ A ⟧ty
    := match A with
       | Base _ => 0
       | A1 ⟶ A2 => plus_ty_nat ∘wm ⟨ const_wm (sum_lvf A2) , lvf ⟩
       end.

  (** ** Interpretation of application *)
  Definition p_app_fun
             {A1 A2 : ty B}
    : ⟦ A1 ⟶ A2 ⟧ty * ⟦ A1 ⟧ty -> ⟦ A2 ⟧ty
    := fun z =>
         let f := fst z in
         let x := snd z in
         (sum_lvf A2 +c (lvf f + lvf x)) +f f x.

  Global Instance weakMonotone_p_app_fun
                  (A₁ A₂ : ty B)
    : @weakMonotone
        (⟦ A₁ ⟶ A₂ ⟧ty * ⟦ A₁ ⟧ty)
        ⟦ A₂ ⟧ty
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
        ** apply lvf.
           apply p.
        ** apply lvf.
           apply p.
    - cbn.
      cbn in p.
      destruct p as [ p1 p2 ].
      refine (ge_trans (p1 _) _).
      apply map_ge.
      apply p2.
  Qed.
  
  Definition p_app
             (A₁ A₂ : ty B)
    : ⟦ A₁ ⟶ A₂ ⟧ty * ⟦ A₁ ⟧ty →wm ⟦ A₂ ⟧ty
    := @make_monotone
         (⟦ A₁ ⟶ A₂ ⟧ty * ⟦ A₁ ⟧ty)
         ⟦ A₂ ⟧ty
         p_app_fun
         _.

  Proposition p_app_ge_id
              (A₁ A₂ : ty B)
              (f : ⟦ A₁ ⟧ty →wm ⟦ A₂ ⟧ty)
              (x : ⟦ A₁ ⟧ty)
    : p_app_fun (f , x) >= f x.
  Proof.
    unfold p_app_fun ; cbn.
    apply plus_ty_ge_right.
    apply ge_refl.
  Qed.

  Proposition p_app_strict_l
              (A₁ A₂ : ty B)
              (f₁ f₂ : ⟦ A₁ ⟧ty →wm ⟦ A₂ ⟧ty)
              (x : ⟦ A₁ ⟧ty)
              (p : f₁ > f₂)
    : p_app_fun (f₁ , x) > p_app_fun (f₂ , x).
  Proof.
    unfold p_app_fun ; cbn.
    apply plus_ty_strict_monotonic.
    - apply plus_ty_nat_strict_monotone.
      cbn.
      enough (lvf (f₁ (min_el_ty A₁))
              >
              lvf (f₂ (min_el_ty A₁)))
        as H.
      {
        cbn in H.
        nia.
      }
      apply lvf_strict_monotonic.
      apply p.
    - apply p.
  Qed.

  Proposition p_app_strict_r
              (A₁ A₂ : ty B)
              (f : ⟦ A₁ ⟧ty →wm ⟦ A₂ ⟧ty)
              (x₁ x₂ : ⟦ A₁ ⟧ty)
              (p : x₁ > x₂)
    : p_app_fun (f , x₁) > p_app_fun (f , x₂).
  Proof.
    unfold p_app_fun ; cbn.
    apply plus_ty_strict_weak_monotonic.
    - apply plus_ty_nat_strict_monotone.
      enough (lvf x₁
              >
              lvf x₂)
        as H.
      {
        cbn ; cbn in H.
        nia.
      }
      apply lvf_strict_monotonic.
      exact p.
    - apply map_ge.
      apply compat.
      exact p.
  Qed.

  Notation "⟦ t ⟧tm" := (sem_Tm p_base p_fun_sym p_app t).

  (** ** Compatibility requirement *)
  Definition poly_WMalgebra_rewrite_rules
             (H : forall (r : rewriteRules X)
                         (x : ⟦ vars r ⟧con),
                  ⟦ lhs r ⟧tm x > ⟦ rhs r ⟧tm x)
             (r : rewriteRules X)
             (C : con B)
             (s : sub (arity X) C (vars r))
             (x : ⟦ C ⟧con)
    : ⟦ lhs r [ s ] ⟧tm x > ⟦ rhs r [ s ] ⟧tm x.
  Proof.
    rewrite !sub_Lemma.
    apply H.
  Qed.

  (** ** Interpretation from polynomials *)
  Definition poly_InterpretationData
    : InterpretationData X.
  Proof.
    simple refine (make_InterpretationData
                     X
                     p_base
                     _
                     (fun _ => 0)
                     (fun _ => nat_Wf)
                     p_fun_sym
                     p_app
                     _
                     _
                     _).
    - exact p_app_strict_l.
    - exact p_app_strict_r.
    - exact p_app_ge_id.
  Defined.

  Definition poly_strong_reduction_pair
    : strong_reduction_pair (arity X).
  Proof.
    apply interpretation_to_strong_reduction_pair.
    exact poly_InterpretationData.
  Defined.

  Definition poly_Interpretation
             (H : forall (r : rewriteRules X)
                         (x : ⟦ vars r ⟧con),
                  ⟦ lhs r ⟧tm x > ⟦ rhs r ⟧tm x)
    : Interpretation X.
  Proof.
    simple refine (make_Interpretation _ _ _ _ _).
    - exact poly_InterpretationData.
    - exact (poly_WMalgebra_rewrite_rules H).
  Defined.
End PolyAlgebra.