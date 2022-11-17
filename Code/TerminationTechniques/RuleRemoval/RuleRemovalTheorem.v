Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Nijn.TerminationTechniques.RuleRemoval.RuleSelector.
Require Import List.

Import AFSNotation.

Section RuleRemoval.
  Context {B F : Type}
          `{decEq B}
          `{decEq F}
          {X : afs B F}
          (P : selector X)
          (srp : strong_reduction_pair (arity X))
          (H_srp : respects_selector X srp P)
          (HX : isSN (remove_afs X P)).

  Definition rule_removal_to_lexico
             {C : con B}
             {A : ty B}
             (t : tm X C A)
    : tm X C A * tm X C A
    := (t , t).
  
  Definition rule_removal_rewrite_lexico
             {C : con B}
             {A : ty B}
             {t₁ t₂ : tm X C A}
             (p : t₁ ∼> t₂)
    : lexico
        (term_CompatRel _ C A srp)
        (fun (t₁ t₂ : (tm X C A)) => rew (remove_afs X P) t₁ t₂)
        (rule_removal_to_lexico t₁)
        (rule_removal_to_lexico t₂).
  Proof.
    induction p.
    - induction r.
      + (* App_l *)
        destruct IHr as [IHr | [IHr1 IHr2]].
        * left ; simpl.
          apply app_gt_l.
          ** apply srp.
          ** exact IHr.
        * simpl in IHr1, IHr2.
          right ; simpl.
          split.
          ** apply app_ge.
             *** apply srp.
             *** apply IHr1.
             *** apply srp.
          ** apply rew_App_l.
             exact IHr2.
      + (* Rew_App_r *)
        destruct IHr as [IHr | [IHr1 IHr2]].
        * left ; simpl.
          apply app_gt_r.
          ** apply srp.
          ** exact IHr.
        * right ; simpl.
          simpl in IHr1, IHr2.
          split.
          ** apply app_ge.
             *** apply srp.
             *** apply srp.
             *** apply IHr1.
          ** apply rew_App_r.
             exact IHr2.
      + (* Rew_Lam *)
        destruct IHr as [IHr | [IHr1 IHr2]].
        * left ; simpl ; simpl in IHr.
          apply lam_gt.
          ** apply srp.
          ** exact IHr.
        * right ; simpl.
          simpl in IHr1, IHr2.
          split.
          ** intros.
             apply lam_ge.
             *** apply srp.
             *** apply IHr1.
          ** apply rew_Lam.
             exact IHr2.
      + induction r.
        * induction b.
          right ; simpl.
          split.
          ** apply beta_ge.
             apply srp.
          ** apply rew_betaRed.
        * destruct H_srp as [ H_srp_1 H_srp_2 ].
          destruct (dec_selector_members X P r) as [ d | d ].
          ** left.
             cbn.
             apply sub_gt.
             *** apply srp.
             *** apply H_srp_1.
                 assumption.
          ** right.
             split ; cbn.
             *** apply sub_ge.
                 **** apply srp.
                 **** apply H_srp_2.
                      assumption.
             *** assert (In (member_el r) (remove_rewrite_rules X P)) as Hrew.
                 {
                   apply In_remove_list_member.
                   exact d.
                 }
                 apply (rew_rewrite_rule
                          (remove_afs X P)
                          (MakeMem (member_el r) Hrew)).
    - (* Trans *)
      refine (lexico_trans _ _ _ _ _).
      + apply srp.
      + intros ? ? ? q1 q2.
        exact (rew_Trans q1 q2).
      + apply IHp1.
      + apply IHp2.
  Qed.

  Theorem rule_removal
    : isSN X.
  Proof.
    intros C A.
    simple refine (fiber_Wf _ _ _).
    - exact (term_CompatRel _ C A srp * tm X C A)%type.
    - exact (lexico
               (term_CompatRel _ C A srp)
               (fun (t₁ t₂ : (tm X C A)) => rew (remove_afs X P) t₁ t₂)).
    - apply lexico_Wf.
      + apply srp.
      + apply srp.
      + apply HX.
    - apply rule_removal_to_lexico.
    - intros t₁ t₂ p.
      exact (rule_removal_rewrite_lexico p).
  Defined.
End RuleRemoval.
