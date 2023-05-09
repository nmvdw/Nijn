Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Nijn.Interpretation.OrderInterpretation.
Require Import Nijn.TerminationTechniques.RuleRemoval.RuleSelector.

Require Import Lia.

(** * The polynomial method *)

(** We start by defining polynomials. To do that, we define both base polynomials and arbitrary polynomials and that we can convert between base polynomials and polynomials of a base type. Since base polynomials do not keep track of the type, we can freely add and multiply them without worrying about whether their types are actually the same. *)
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

(** ** Polynomial interpretation *)
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

  (** ** Minimal element of interpretations of types *)
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

  Proposition plus_ty_nat_strict_monotone_l
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

  Proposition plus_ty_nat_strict_monotone_r
              {A : ty B}
              {x x' : ⟦ A ⟧ty}
              (y : nat_CompatRel)
              (p : x > x')
    : x +c y > x' +c y.
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - cbn in p.
      lia.
    - intros z.
      apply IHA₂.
      apply p.
  Qed.

  Proposition plus_ty_nat_ge
              {A : ty B}
              (x : ⟦ A ⟧ty)
              (y : nat_CompatRel)
    : x +c y >= x.
  Proof.
    induction A as [ b | A₁ IHA₁ A₂ IHA₂ ] ; cbn.
    - lia.
    - intros z.
      apply IHA₂.
  Qed.

  (** ** Interpretation of application *)
  Definition p_app
             {A1 A2 : ty B}
    : ⟦ A1 ⟶ A2 ⟧ty * ⟦ A1 ⟧ty →wm ⟦ A2 ⟧ty
    := let f := fst_wm in
       let x := snd_wm in
       plus_ty_nat ∘wm ⟨ f ·wm x , lvf ∘wm x ⟩.

  Definition p_app'
             (A1 A2 : ty B)
    : ⟦ A1 ⟶ A2 ⟧ty * ⟦ A1 ⟧ty →wm ⟦ A2 ⟧ty
    := p_app.
  
  Proposition p_app_ge_id
              (A₁ A₂ : ty B)
              (f : ⟦ A₁ ⟧ty →wm ⟦ A₂ ⟧ty)
              (x : ⟦ A₁ ⟧ty)
    : p_app (f , x) >= f x.
  Proof.
    apply plus_ty_nat_ge.
  Qed.

  Proposition p_app_strict_l
              (A₁ A₂ : ty B)
              (f₁ f₂ : ⟦ A₁ ⟧ty →wm ⟦ A₂ ⟧ty)
              (x : ⟦ A₁ ⟧ty)
              (p : f₁ > f₂)
    : p_app (f₁ , x) > p_app (f₂ , x).
  Proof.
    unfold p_app ; cbn.
    apply plus_ty_nat_strict_monotone_r.
    apply p.
  Qed.

  Proposition p_app_strict_r
              (A₁ A₂ : ty B)
              (f : ⟦ A₁ ⟧ty →wm ⟦ A₂ ⟧ty)
              (x₁ x₂ : ⟦ A₁ ⟧ty)
              (p : x₁ > x₂)
    : p_app (f , x₁) > p_app (f , x₂).
  Proof.
    unfold p_app ; cbn.
    simple refine (ge_gt _ _).
    - exact (f x₂ +c lvf x₁).
    - apply map_ge.
      split.
      + cbn.
        apply map_ge.
        apply compat.
        exact p.
      + apply ge_refl.
    - apply plus_ty_nat_strict_monotone_l.
      apply (lvf_strict_monotonic p).
  Qed.

  Notation "⟦ t ⟧tm" := (sem_Tm p_base p_fun_sym p_app' t).

  (** ** Compatibility requirement *)
  Definition poly_WMalgebra_rewrite_rule
             (r : rewriteRules X)
             (Hr : forall (x : ⟦ vars r ⟧con),
                     ⟦ lhs r ⟧tm x > ⟦ rhs r ⟧tm x)
             (C : con B)
             (s : sub (arity X) C (vars r))
             (x : ⟦ C ⟧con)
    : ⟦ lhs r [ s ] ⟧tm x > ⟦ rhs r [ s ] ⟧tm x.
  Proof.
    rewrite !sub_Lemma.
    apply Hr.
  Qed.

  Definition poly_WMalgebra_rewrite_rule_ge
             (r : rewriteRules X)
             (Hr : forall (x : ⟦ vars r ⟧con),
                     ⟦ lhs r ⟧tm x >= ⟦ rhs r ⟧tm x)
             (C : con B)
             (s : sub (arity X) C (vars r))
             (x : ⟦ C ⟧con)
    : ⟦ lhs r [ s ] ⟧tm x >= ⟦ rhs r [ s ] ⟧tm x.
  Proof.
    rewrite !sub_Lemma.
    apply Hr.
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
                     p_app'
                     _
                     _
                     _).
    - exact p_app_strict_l.
    - exact p_app_strict_r.
    - exact p_app_ge_id.
  Defined.

  Definition poly_Interpretation
             (H : forall (r : rewriteRules X)
                         (x : ⟦ vars r ⟧con),
                  ⟦ lhs r ⟧tm x > ⟦ rhs r ⟧tm x)
    : Interpretation X.
  Proof.
    simple refine (make_Interpretation _ _ _ _ _).
    - exact poly_InterpretationData.
    - abstract
        (intros ;
         apply poly_WMalgebra_rewrite_rule ;
         apply H).
  Defined.

  (** ** Strong reduction pairs from polynomials *)
  Definition poly_strong_reduction_pair
    : strong_reduction_pair (arity X).
  Proof.
    apply interpretation_to_strong_reduction_pair.
    exact poly_InterpretationData.
  Defined.

  Definition poly_SelectorInterpretation
             `{decEq B}
             `{decEq F}
             (P : selector X)
             (H_gt : forall (r : rewriteRules X)
                            (x : ⟦ vars r ⟧con),
                       selector_members P r
                       -> ⟦ lhs r ⟧tm x > ⟦ rhs r ⟧tm x)
             (H_ge : forall (r : rewriteRules X)
                            (x : ⟦ vars r ⟧con),
                       ~(selector_members P r)
                       -> ⟦ lhs r ⟧tm x >= ⟦ rhs r ⟧tm x)
    : SelectorInterpretation X P.
  Proof.
    refine {| s_inter := poly_InterpretationData ;
             semR_gt := _ ;
             semR_ge := _|}.
    - abstract
        (intros r C s x Hr ;
         apply poly_WMalgebra_rewrite_rule ;
         intro ;
         apply (H_gt r _ Hr)).
    - abstract
        (intros r C s x Hr ;
         apply poly_WMalgebra_rewrite_rule_ge ;
         intro ;
         apply (H_ge r _ Hr)).
  Defined.
End PolyAlgebra.
