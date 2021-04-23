Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.
Require Import Syntax.Signature.TermWeakenings.
Require Import Syntax.Signature.TermSubstitutions.
Require Import Coq.Program.Equality.

(** * Laws for weakenings *)

(** Unitality *)
Proposition wk_id_l
            {B : Type}
            {C1 C2 : con B}
            (w : wk C1 C2)
  : compWk (idWk C2) w = w.
Proof.
  induction w as [ | ? ? ? w IHw | ? ? ? w IHw ]
  ; simpl ; cbn.
  - reflexivity.
  - rewrite IHw.
    reflexivity.
  - rewrite IHw.
    reflexivity.
Qed.

Proposition wk_id_r
            {B : Type}
            {C1 C2 : con B}
            (w : wk C1 C2)
  : compWk w (idWk C1) = w.
Proof.
  induction w as [ | ? ? ? w IHw | ? ? ? w IHw ]
  ; simpl ; cbn.
  - reflexivity.
  - rewrite IHw.
    reflexivity.
  - rewrite IHw.
    reflexivity.
Qed.

(** Associativity *)
Proposition wk_assoc
            {B : Type}
            {C1 C2 C3 C4 : con B}
            (w3 : wk C3 C4)
            (w2 : wk C2 C3)
            (w1 : wk C1 C2)
  : compWk (compWk w3 w2) w1
    =
    compWk w3 (compWk w2 w1).
Proof.
  revert w2 w3.
  revert C3 C4.
  induction w1 as [ | ? ? ? w1 IHw1 | ? ? ? w1 IHw1 ]
  ; intros C3 C4 w2 w3.
  - simpl ; cbn.
    reflexivity.
  - dependent induction w2 ; dependent induction w3 ; simpl ; cbn
    ; rewrite IHw1 ; reflexivity.
  - simpl ; cbn.
    rewrite IHw1.
    reflexivity.
Qed.

(** Functoriality of weakening *)
Proposition wkVar_id
            {B : Type}
            {C : con B}
            {A : ty B}
            (v : var C A)
  : wkVar v (idWk _) = v.
Proof.
  induction v ; simpl ; cbn.
  - reflexivity.
  - rewrite IHv.
    reflexivity.
Qed.

Proposition wkTm_id
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A : ty B}
            (t : tm ar C A)
  : wkTm t (idWk _) = t.
Proof.
  induction t ; simpl.
  - reflexivity.
  - f_equal.
    apply wkVar_id.
  - f_equal.
    exact IHt.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.

Proposition wkVar_comp
            {B : Type}
            {C1 C2 C3 : con B}
            {A : ty B}
            (v : var C3 A)
            (w1 : wk C1 C2)
            (w2 : wk C2 C3)
  : wkVar (wkVar v w2) w1 = wkVar v (compWk w2 w1).
Proof.
  revert w2 v.
  revert C3.
  induction w1 ; intros C3 w2 v.
  - simpl ; cbn.
    reflexivity.
  - dependent induction w2.
    + dependent induction v ; simpl ; cbn.
      * reflexivity.
      * f_equal.
        apply IHw1.
    + simpl ; cbn.
      f_equal.
      apply IHw1.
  - simpl ; cbn.
    f_equal.
    apply IHw1.
Qed.

Proposition wkTm_comp
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 : con B}
            {A : ty B}
            (t : tm ar C3 A)
            (w1 : wk C1 C2)
            (w2 : wk C2 C3)
  : wkTm (wkTm t w2) w1 = wkTm t (compWk w2 w1).
Proof.
  revert w1 w2.
  revert C1 C2.
  induction t ; simpl ; intros C1 C2 w1 w2.
  - reflexivity.
  - f_equal.
    apply wkVar_comp.
  - f_equal.
    apply IHt.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.

(** Weakening can be written as substitution *)
Proposition wkToSub_id
            {B : Type}
            {C : con B}
            {F : Type}
            {ar : F -> ty B}
  : wkToSub (idWk C) = idSub C ar.
Proof.
  induction C as [ | A C IHC ].
  - reflexivity.
  - simpl.
    rewrite IHC.
    reflexivity.
Qed.

Proposition subVar_drop
            {B : Type}
            {C2 : con B}
            {A1 A2 : ty B}
            {F : Type}
            {ar : F -> ty B}
            (v : var C2 A1)
            {C1 : con B}
            (s : sub ar C1 C2)
  : subVar v (dropSub A2 s)
    =
    subVar (Vs v) (keepSub A2 s).
Proof.
  induction s.
  - reflexivity.
  - dependent induction v ; simpl ; cbn.
    + reflexivity.
    + rewrite IHs.
      reflexivity.
Qed.

Proposition subVar_keep
            {B : Type}
            {C2 : con B}
            {A1 A2 : ty B}
            {F : Type}
            {ar : F -> ty B}
            (v : var C2 A1)
            {C1 : con B}
            (s : sub ar C1 C2)
  : subVar (Vs v) (keepSub A2 s)
    =
    wkTm (subVar v s) (Drop A2 (idWk C1)).
Proof.
  induction s.
  - inversion v.
  - dependent induction v ; simpl ; cbn.
    + reflexivity.
    + rewrite <- IHs.
      apply subVar_drop.
Qed.

Proposition wkVar_is_subVar
            {B : Type}
            {C2 : con B}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            (v : var C2 A)
            {C1 : con B}
            (w : wk C1 C2)
  : @TmVar B F ar _ _ (wkVar v w) = subVar v (wkToSub w).
Proof.
  induction w.
  - inversion v.
  - dependent induction v ; simpl ; cbn.
    + reflexivity.
    + rewrite subVar_drop.
      rewrite subVar_keep.
      simpl ; cbn.
      rewrite <- (IHw v).
      simpl ; cbn.
      rewrite wkVar_id.
      reflexivity.
  - simpl ; cbn.
    rewrite subVar_drop.
    rewrite subVar_keep.
    simpl ; cbn.
    rewrite <- (IHw v).
    simpl ; cbn.
    rewrite wkVar_id.
    reflexivity.
Qed.
    
Proposition wkTm_is_subTm
            {B : Type}
            {C2 : con B}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            (t : tm ar C2 A)
            {C1 : con B}
            (w : wk C1 C2)
  : wkTm t w = subTm t (wkToSub w).
Proof.
  revert w.
  revert C1.
  induction t ; intros C1 w ; simpl.
  - reflexivity.
  - apply wkVar_is_subVar.
  - simpl.
    rewrite IHt.
    reflexivity.
  - simpl.
    rewrite IHt1.
    rewrite IHt2.
    reflexivity.
Qed.

(** * Laws for substitution *)

(** Action of identity substitution *)
Proposition subVar_id
            {B : Type}
            {C : con B}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            (v : var C A)
  : subVar v (idSub C ar) = TmVar v.
Proof.
  induction C as [ | A' C IHC ].
  - inversion v.
  - dependent induction v ; simpl ; cbn.
    + reflexivity.
    + rewrite subVar_drop.
      rewrite subVar_keep.
      rewrite IHC.
      simpl.
      rewrite wkVar_id.
      reflexivity.
Qed.

Proposition subTm_id
            {B : Type}
            {C : con B}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            (t : tm ar C A)
  : subTm t (idSub C ar) = t.
Proof.
  induction t ; simpl.
  - reflexivity.
  - apply subVar_id.
  - simpl.
    f_equal.
    exact IHt.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.

(** Right unitality *)
Proposition Sub_id_right
            {B : Type}
            {C1 C2 : con B}
            {F : Type}
            {ar : F -> ty B}
            (s : sub ar C1 C2)
  : compSub s (idSub _ _) = s.
Proof.
  induction s.
  - reflexivity.
  - simpl ; cbn.
    rewrite IHs.
    f_equal.
    rewrite <- wkTm_id.
    rewrite wkTm_is_subTm.
    f_equal.
    rewrite wkToSub_id.
    reflexivity.
Qed.

(** We can already compute substitutions on compositions for variables *)
Proposition subVar_comp
            {B : Type}
            {C3 : con B}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            (v : var C3 A)
            {C1 C2 : con B}
            (s1 : sub ar C1 C2)
            (s2 : sub ar C2 C3)
  : subTm (subVar v s2) s1 = subVar v (compSub s2 s1).
Proof.
  induction s2.
  - inversion v.
  - dependent induction v ; simpl ; cbn.
    + reflexivity.
    + apply IHs2.
Qed.

(** For the remainder, we will make use of the following definitions *)
Definition compWkSub
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 C3 : con B}
           (w : wk C2 C3)
           (s : sub ar C1 C2)
  : sub ar C1 C3.
Proof.
  induction w.
  - exact s.
  - inversion s ; subst.
    refine (_ & _).
    + apply IHw.
      exact X.
    + exact X0.
  - inversion s ; subst.
    apply IHw.
    exact X.
Defined.

Definition compSubWk
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C1 C2 C3 : con B}
           (s : sub ar C2 C3)
           (w : wk C1 C2)
  : sub ar C1 C3.
Proof.
  induction s.
  - apply ToEmpty.
  - exact (IHs w & wkTm t w).
Defined.    

Definition dropId
           {B : Type}
           (C : con B)
           (A : ty B)
  : wk (A ,, C) C
  := Drop A (idWk C).

(** Some lemmas on these definitions *)
Proposition dropSub_is_compSubWk
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (A : ty B)
            (s : sub ar C1 C2)
  : dropSub A s = compSubWk s (dropId _ _).
Proof.
  induction s.
  - simpl ; cbn.
    reflexivity.
  - simpl ; cbn.
    rewrite IHs.
    reflexivity.
Qed.

Proposition assoc_compSubwk
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 C4 : con B}
            (w1 : wk C1 C2)
            (w2 : wk C2 C3)
            (s3 : sub ar C3 C4)
  : compSubWk (compSubWk s3 w2) w1
    =
    compSubWk s3 (compWk w2 w1).
Proof.
  induction s3.
  - reflexivity.
  - simpl ; cbn.
    rewrite IHs3.
    f_equal.
    apply wkTm_comp.
Qed.

Proposition compSubwk_is_compSub
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 : con B}
            (w1 : wk C1 C2)
            (s2 : sub ar C2 C3)
  : compSubWk s2 w1 = compSub s2 (wkToSub w1).
Proof.
  induction s2.
  - reflexivity.
  - simpl ; cbn.
    rewrite IHs2.
    f_equal.
    rewrite wkTm_is_subTm.
    reflexivity.
Qed.

Proposition wkTmSubTm
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 : con B}
            (w1 : wk C1 C2)
            (s2 : sub ar C2 C3)
            {A : ty B}
            (t : tm ar C3 A)
  : subTm t (compSubWk s2 w1) = wkTm (subTm t s2) w1.
Proof.
  revert w1 s2.
  revert C1 C2.
  induction t ; intros C1 C2 w1 s2.
  - reflexivity.
  - simpl ; cbn.
    rewrite wkTm_is_subTm.
    rewrite subVar_comp.
    f_equal.
    rewrite compSubwk_is_compSub.
    reflexivity.
  - simpl ; cbn.
    specialize (IHt _ _ (Keep A1 w1) (keepSub A1 s2)).
    simpl in IHt ; cbn in IHt.
    rewrite <- IHt ; clear IHt.
    unfold keepSub.
    do 3 f_equal.
    rewrite !dropSub_is_compSubWk.
    rewrite !assoc_compSubwk.
    f_equal.
    simpl ; cbn.
    f_equal.
    rewrite wk_id_l, wk_id_r.
    reflexivity.
  - simpl ; cbn.
    rewrite IHt1, IHt2.
    reflexivity.
Qed.

Proposition compSubwk_assoc
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 C4 : con B}
            (w1 : wk C1 C2)
            (s2 : sub ar C2 C3)
            (s3 : sub ar C3 C4)
  : compSubWk (compSub s3 s2) w1
    =
    compSub s3 (compSubWk s2 w1).
Proof.
  induction s3.
  - reflexivity.
  - simpl ; cbn.
    rewrite IHs3.
    f_equal.
    rewrite wkTmSubTm.
    reflexivity.
Qed.

Proposition compWkSub_id
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (s : sub ar C1 C2)
  : compWkSub (idWk _) s = s.
Proof.
  induction s.
  - reflexivity.
  - simpl ; cbn.
    rewrite IHs.
    reflexivity.
Qed.

Proposition compWkSubWk
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 C4 : con B}
            (w1 : wk C1 C2)
            (s2 : sub ar C2 C3)
            (w3 : wk C3 C4)
  : compSubWk (compWkSub w3 s2) w1
    =
    compWkSub w3 (compSubWk s2 w1).
Proof.
  revert w1 s2.
  revert C1 C2.
  induction w3 ; intros ? ? w1 s2.
  - reflexivity.
  - dependent destruction s2.
    simpl ; cbn.
    rewrite IHw3.
    reflexivity.
  - dependent destruction s2.
    simpl ; cbn.
    apply IHw3.
Qed.

Proposition subTm_wkTm
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 : con B}
            (s1 : sub ar C1 C2)
            (w2 : wk C2 C3)
            {A : ty B}
            (t : tm ar C3 A)
  : subTm t (compWkSub w2 s1) = subTm (wkTm t w2) s1.
Proof.
  revert s1 w2.
  revert C1 C2.
  induction t ; intros C1 C2 s1 w2.
  - reflexivity.
  - simpl ; cbn.
    induction w2.
    + reflexivity.
    + dependent destruction s1 ; dependent destruction v ; simpl ; cbn.
      * reflexivity.
      * apply IHw2.
    + dependent destruction s1.
      exact (IHw2 v s1).
  - simpl ; cbn.
    specialize (IHt _ _ (keepSub A1 s1) (Keep A1 w2)).
    rewrite <- IHt ; clear IHt.
    unfold keepSub ; simpl ; cbn.
    do 3 f_equal.
    rewrite !dropSub_is_compSubWk.
    rewrite !compWkSubWk.
    reflexivity.
  - simpl ; cbn.
    rewrite IHt1, IHt2.
    reflexivity.
Qed.

Proposition compSub_compWkSub
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 C4 : con B}
            (s1 : sub ar C1 C2)
            (w2 : wk C2 C3)
            (s3 : sub ar C3 C4)
  : compSub s3 (compWkSub w2 s1)
    =
    compSub (compSubWk s3 w2) s1.
Proof.
  induction s3.
  - simpl ; cbn.
    reflexivity.
  - simpl ; cbn.
    rewrite IHs3.
    f_equal.
    rewrite subTm_wkTm.
    reflexivity.
Qed.

(** Now we prove the remaining laws that are necessary *)

(** Left unitality *)
Proposition Sub_id_left
            {B : Type}
            {C1 C2 : con B}
            {F : Type}
            {ar : F -> ty B}
            (s : sub ar C1 C2)
  : compSub (idSub _ _) s = s.
Proof.
  induction s.
  - reflexivity.
  - simpl ; cbn.
    f_equal.
    rewrite !dropSub_is_compSubWk.
    rewrite <- compSub_compWkSub.
    simpl ; cbn.
    rewrite compWkSub_id.
    exact IHs.
Qed.

(** Composition of substitutions *)
Proposition subTm_comp
            {B : Type}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 : con B}
            (t : tm ar C3 A)
            (s1 : sub ar C1 C2)
            (s2 : sub ar C2 C3)
  : subTm (subTm t s2) s1 = subTm t (compSub s2 s1).
Proof.
  revert s2 s1.
  revert C1 C2.
  induction t ; simpl ; intros C1 C2 s1 s2.
  - reflexivity.
  - apply subVar_comp.
  - rewrite (IHt _ _ (keepSub A1 s1) (keepSub A1 s2)) ; clear IHt.
    simpl ; cbn ; unfold keepSub.
    do 3 f_equal.
    rewrite !dropSub_is_compSubWk.
    rewrite compSubwk_assoc.
    symmetry.
    etransitivity.
    {
      apply f_equal.
      symmetry.
      apply compWkSub_id.
    }
    pose (compSub_compWkSub (keepSub A1 s2) (dropId _ _) s1) as e.
    unfold keepSub in e.
    simpl in e ; cbn in e.
    rewrite dropSub_is_compSubWk in e.
    exact e.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.

(** Needed when we apply beta reduction *)
Proposition beta_sub_help
            {B : Type}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 : con B}
            (t : tm ar C2 A)
            (w : wk C1 C2)
  : compSub
      (wkToSub (Keep _ w))
      (idSub _ _ & subTm t (wkToSub w))
    =
    compSub (idSub _ ar & t) (wkToSub w).
Proof.
  simpl ; cbn.
  rewrite Sub_id_left.
  f_equal.
  simpl ; cbn.
  rewrite !dropSub_is_compSubWk.
  rewrite <- compSub_compWkSub.
  simpl ; cbn.
  rewrite compWkSub_id.
  rewrite Sub_id_right.
  reflexivity.
Qed.

(** Associativity of substitution *)
Proposition subTm_assoc
            {B : Type}
            {A : ty B}
            {F : Type}
            {ar : F -> ty B}
            {C1 C2 C3 C4 : con B}
            (s1 : sub ar C1 C2)
            (s2 : sub ar C2 C3)
            (s3 : sub ar C3 C4)
  : compSub s3 (compSub s2 s1)
    =
    compSub (compSub s3 s2) s1.
Proof.
  induction s3 ; simpl ; cbn.
  - reflexivity.
  - rewrite IHs3.
    f_equal.
    rewrite subTm_comp.
    reflexivity.
Qed.
