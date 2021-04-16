Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.
Require Import Syntax.Signature.TermWeakenings.
Require Import Syntax.Signature.TermSubstitutions.
Require Import Coq.Program.Equality.

(** Laws for weakenings *)

(** Unitality *)
Proposition wk_id_l
            {B : Type}
            {C1 C2 : Con B}
            (w : Wk C1 C2)
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
            {C1 C2 : Con B}
            (w : Wk C1 C2)
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
            {C1 C2 C3 C4 : Con B}
            (w3 : Wk C3 C4)
            (w2 : Wk C2 C3)
            (w1 : Wk C1 C2)
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
            {C : Con B}
            {A : Ty B}
            (v : Var C A)
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
            {ar : F -> Ty B}
            {C : Con B}
            {A : Ty B}
            (t : Tm ar C A)
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
            {C1 C2 C3 : Con B}
            {A : Ty B}
            (v : Var C3 A)
            (w1 : Wk C1 C2)
            (w2 : Wk C2 C3)
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
            {ar : F -> Ty B}
            {C1 C2 C3 : Con B}
            {A : Ty B}
            (t : Tm ar C3 A)
            (w1 : Wk C1 C2)
            (w2 : Wk C2 C3)
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
            {C : Con B}
            {F : Type}
            {ar : F -> Ty B}
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
            {C2 : Con B}
            {A1 A2 : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (v : Var C2 A1)
            {C1 : Con B}
            (s : Sub ar C1 C2)
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
            {C2 : Con B}
            {A1 A2 : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (v : Var C2 A1)
            {C1 : Con B}
            (s : Sub ar C1 C2)
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
            {C2 : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (v : Var C2 A)
            {C1 : Con B}
            (w : Wk C1 C2)
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
            {C2 : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (t : Tm ar C2 A)
            {C1 : Con B}
            (w : Wk C1 C2)
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

(** Laws for substitution *)

Proposition comp_keepSub
            {B : Type}
            {C1 C2 C3 : Con B}
            {F : Type}
            {ar : F -> Ty B}
            {A : Ty B}
            (s1 : Sub ar C1 C2)
            (s2 : Sub ar C2 C3)
  : compSub (keepSub A s2) (keepSub A s1)
    =
    keepSub A (compSub s2 s1).
Proof.
  unfold keepSub.
  simpl ; cbn.
  f_equal.
  induction s2.
  - reflexivity.
  - simpl.
    rewrite IHs2 ; clear IHs2.
    f_equal.
Admitted.

Proposition subVar_comp
            {B : Type}
            {C3 : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (v : Var C3 A)
            {C1 C2 : Con B}
            (s1 : Sub ar C1 C2)
            (s2 : Sub ar C2 C3)
  : subTm (subVar v s2) s1 = subVar v (compSub s2 s1).
Proof.
  induction s2.
  - inversion v.
  - dependent induction v ; simpl ; cbn.
    + reflexivity.
    + apply IHs2.
Qed.

Proposition subTm_comp
            {B : Type}
            {C3 : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (t : Tm ar C3 A)
            {C1 C2 : Con B}
            (s1 : Sub ar C1 C2)
            (s2 : Sub ar C2 C3)
  : subTm (subTm t s2) s1 = subTm t (compSub s2 s1).
Proof.
  revert s2 s1.
  revert C1 C2.
  induction t ; simpl ; intros C1 C2 s1 s2.
  - reflexivity.
  - apply subVar_comp.
  - rewrite IHt.
    do 2 f_equal.
    apply comp_keepSub.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.

Proposition subVar_id
            {B : Type}
            {C : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (v : Var C A)
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

Proposition comp_drop
            {B : Type}
            {C1 C2 C3 : Con B}
            {F : Type}
            {ar : F -> Ty B}
            (s1 : Sub ar C1 C2)
            (s2 : Sub ar C2 C3)
            {A : Ty B}
            (t : Tm ar C1 A)
  : compSub (dropSub A s2) (s1 & t) = compSub s2 s1.
Proof.
  induction s2.
  - reflexivity.
  - simpl ; cbn.
    rewrite IHs2.
    f_equal.
    rewrite wkTm_is_subTm.
    rewrite subTm_comp.
    f_equal.
    (*
rewrite IHs2.
    reflexivity.
     *)
Admitted.

Proposition Sub_id_left
            {B : Type}
            {C1 C2 : Con B}
            {F : Type}
            {ar : F -> Ty B}
            (s : Sub ar C1 C2)
  : compSub (idSub _ _) s = s.
Proof.
  revert s.
  revert C1.
  induction C2 ; intros C1 s.
  - cbn.
    dependent induction s.
    reflexivity.
  - simpl.
    dependent induction s.
    simpl ; cbn.
    f_equal.
    rewrite comp_drop.
    apply IHC2.
Qed.

Proposition Sub_id_right
            {B : Type}
            {C1 C2 : Con B}
            {F : Type}
            {ar : F -> Ty B}
            (s : Sub ar C1 C2)
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

Proposition keep_drop
            {B : Type}
            {C1 C2 : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (s : Sub ar C1 C2)
  : compSub (dropSub A s) (keepSub A (idSub C1 ar))
    =
    dropSub A s.
Proof.
  induction s ; simpl.
  - reflexivity.
  - rewrite IHs ; clear IHs.
    f_equal.
    rewrite wkTm_is_subTm.
    rewrite subTm_comp.
    f_equal.
    exact (Sub_id_right (wkToSub (Drop A (idWk C1)))).
Qed.

Proposition subTm_id
            {B : Type}
            {C : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (t : Tm ar C A)
  : subTm t (idSub C ar) = t.
Proof.
  induction t ; simpl.
  - reflexivity.
  - apply subVar_id.
  - simpl.
    rewrite <- IHt.
    f_equal.
    rewrite !subTm_comp.
    f_equal.
    simpl ; cbn.
    rewrite keep_drop.
    reflexivity.
  - rewrite IHt1, IHt2.
    reflexivity.
Qed.
  
Proposition beta_sub_help
            {B : Type}
            {C1 C2 : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (t : Tm ar C2 A)
            (w : Wk C1 C2)
  : compSub
      (wkToSub (Keep _ w))
      (idSub _ _ & subTm t (wkToSub w))
    =
    compSub (idSub _ ar & t) (wkToSub w).
Proof.
  simpl ; cbn.
  rewrite Sub_id_left.
  f_equal.
  rewrite comp_drop.
  rewrite Sub_id_right.
  reflexivity.
Qed.
