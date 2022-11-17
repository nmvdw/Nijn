Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Nijn.TerminationTechniques.RuleRemoval.
Require Import Nijn.Interpretation.OrderInterpretation.
Require Import Nijn.TerminationTechniques.PolynomialMethod.
Require Import Nijn.TerminationTechniques.NoRules.

Local Open Scope compat.

(** * Certificates *)

(** A certificate is a representation of a proof of strong normalization. As such, the core specification is that from a certificate, one must get a proof of strong normalization. Our certificates allow the following steps:
 - If there are no rewrite rules, then the system is strongly normalizing
 - The polynomial method
 - Rule removal
 Note that for rule removal, we also need another notion of certificate, which we call a rule removal certificate. From this notion of certificate, one must obtain a strong reduction pair that respects the rule selection. For this kind of certificate, we allow the following steps:
 - The polynomial method
 *)
Inductive rule_removal_certificate
          {B F : Type}
          `{decEq B} `{decEq F}
          (X : afs B F)
          (P : selector X)
  : Type
  :=
| PolySRP :
  forall (J : forall (f : F), poly ∙ (arity X f)),
    (forall (r : rewriteRules X)
            (x : sem_Con p_base (vars r)),
       selector_members X P r
       ->
       sem_Tm p_base (p_fun_sym X J) p_app (lhs r) x
       >
       sem_Tm p_base (p_fun_sym X J) p_app (rhs r) x)
    ->
    (forall (r : rewriteRules X)
            (x : sem_Con p_base (vars r)),
       ~(selector_members X P r)
       ->
       sem_Tm p_base (p_fun_sym X J) p_app (lhs r) x
       >=
       sem_Tm p_base (p_fun_sym X J) p_app (rhs r) x)
    -> rule_removal_certificate X P.

Definition rr_certificate_to_srp
           {B F : Type}
           `{decEq B} `{decEq F}
           {X : afs B F}
           {P : selector X}
           (C : rule_removal_certificate X P)
  : strong_reduction_pair (arity X).
Proof.
  induction C as [ J ].
  apply interpretation_to_strong_reduction_pair.
  apply poly_InterpretationData.
  exact J.
Defined.

Theorem rr_certificate_respects_srp
        {B F : Type}
        `{decEq B} `{decEq F}
        {X : afs B F}
        {P : selector X}
        (C : rule_removal_certificate X P)
  : respects_selector X (rr_certificate_to_srp C) P.
Proof.
  induction C as [ J H_gt H_ge ].
  refine (interpretation_respects_selector
            P
            (poly_SelectorInterpretation X J P H_gt H_ge)).
Defined.

Inductive certificate
          {B F : Type}
          `{decEq B} `{decEq F}
          (X : afs B F)
  : Type
  :=
| EmptySN : isNil (list_of_rewriteRules X) -> certificate X
| PolySN :
  forall (J : forall (f : F), poly ∙ (arity X f)),
         (forall (r : rewriteRules X)
                 (x : sem_Con p_base (vars r)),
           sem_Tm p_base (p_fun_sym X J) p_app (lhs r) x
           >
           sem_Tm p_base (p_fun_sym X J) p_app (rhs r) x)
         ->
         certificate X
| RuleRemovalSN :
  forall (P : selector X),
    rule_removal_certificate X P
    -> certificate (remove_afs X P)
    -> certificate X.

Theorem certificate_to_isSN
        {B F : Type}
        `{decEq B}
        `{decEq F}
        {X : afs B F}
        (C : certificate X)
  : isSN X.
Proof.
  induction C as [ ? HX | ? J HJ | ? P srp C IHC ].
  - apply empty_list_SN.
    exact HX.
  - apply afs_is_SN_from_Interpretation.
    exact (poly_Interpretation _ J HJ).
  - simple refine (rule_removal P _ _ IHC).
    + exact (rr_certificate_to_srp srp).
    + apply rr_certificate_respects_srp.
Defined.
