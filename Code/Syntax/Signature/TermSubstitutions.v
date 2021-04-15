Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.
Require Import Syntax.Signature.TermWeakenings.

Inductive Sub {B : Type} {F : Type} : (F -> Ty B) -> Con B -> Con B -> Type :=
| ToEmpty : forall {ar : F -> Ty B} (C : Con B), Sub ar C ∙
| ExtendSub : forall {ar : F -> Ty B} {C1 C2 : Con B} {A : Ty B},
    Sub ar C1 C2 -> Tm ar C1 A -> Sub ar C1 (A ,, C2).

Notation "s & t" := (ExtendSub s t) (at level 30).

Fixpoint dropSub
         {B : Type}
         {C1 C2 : Con B}
         {F : Type}
         {ar : F -> Ty B}
         (A : Ty B)
         (s : Sub ar C1 C2)
  : Sub ar (A ,, C1) C2
  := match s with
     | ToEmpty _ => ToEmpty _
     | s & t => dropSub A s & wkTm t (Drop A (idWk _))
     end.

Definition keepSub
           {B : Type}
           {C1 C2 : Con B}
           {F : Type}
           {ar : F -> Ty B}
           (A : Ty B)
           (s : Sub ar C1 C2)
  : Sub ar (A ,, C1) (A ,, C2)
  := dropSub A s & TmVar Vz.

Fixpoint idSub
         {B : Type}
         (C : Con B)
         {F : Type}
         (ar : F -> Ty B)
         {struct C}
  : Sub ar C C
  := match C with
     | ∙ => ToEmpty _
     | A ,, C => dropSub A (idSub C ar) & TmVar Vz
     end.

Fixpoint wkToSub
         {B : Type}
         {C1 C2 : Con B}
         {F : Type}
         {ar : F -> Ty B}
         (w : Wk C1 C2)
  : Sub ar C1 C2
  := match w with
     | EmptyWk => ToEmpty ∙
     | Keep A w => keepSub A (wkToSub w)
     | Drop A w => dropSub A (wkToSub w)
     end.

Definition subVar
           {B : Type}
           {C1 C2 : Con B}
           {F : Type}
           {ar : F -> Ty B}
           {A : Ty B}
           (v : Var C2 A)
           (s : Sub ar C1 C2)
  : Tm ar C1 A.
Proof.
  induction s.
  - apply TmVar.
    inversion v.
  - inversion v.
    + subst.
      assumption.
    + apply IHs.
      assumption.
Defined.

Fixpoint subTm
         {B : Type}
         {C2 : Con B}
         {A : Ty B}
         {F : Type}
         {ar : F -> Ty B}
         (t : Tm ar C2 A)
  : forall {C1 : Con B}, Sub ar C1 C2 -> Tm ar C1 A
  := match t with
     | BaseTm f => fun _ _ => BaseTm f
     | TmVar v => fun _ s => subVar v s
     | Lam f => fun _ s => Lam (subTm f (keepSub _ s))
     | App f t => fun _ s => App (subTm f s) (subTm t s) 
     end.

Definition compSub
           {B : Type}
           {C1 C2 C3 : Con B}
           {F : Type}
           {ar : F -> Ty B}
           (s2 : Sub ar C2 C3)
           (s1 : Sub ar C1 C2)
  : Sub ar C1 C3.
Proof.
  induction s2 as [ | ? ? ? ? s2 IHs2 t ].
  - apply ToEmpty.
  - exact (IHs2 s1 & subTm t s1).
Defined.

(** LEMMATA ON SUBSTITUTION *)
Require Import Coq.Program.Equality.

Definition wkToSub_id
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

Definition wkVar_is_subVar
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
  (*
  induction w.
  - inversion v.
  - inversion v ; subst.
    + admit.
    + admit.
  - simpl.
    specialize (IHw v).
    inversion v ; subst.
    + simpl.
      cbn.
      specialize (IHw v).
      admit.
    +  simpl.
      rewrite <- 
      rewrite IHw.
      rewrite <- IHw.
      simpl.
      cbn.
  induction v.
  - dependent induction w.
    + reflexivity.
    + simpl.
      specialize (IHw ar _ _ w eq_refl).
      Locate "~=".
      simpl.
      admit.
  -*)
Admitted.
    
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
  - admit.
  - rewrite IHt.
    (*
    rewrite comp_keepSub.
    reflexivity.
     *)
    admit.
  - rewrite IHt1, IHt2.
    reflexivity.
Admitted.


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
  simpl.
  cbn.
  f_equal.
  induction s2.
  - reflexivity.
  - simpl.
    rewrite IHs2 ; clear IHs2.
    f_equal.
    rewrite !wkTm_is_subTm.
    rewrite !subTm_comp.
    f_equal.
    simpl ; cbn.
    rewrite !wkToSub_id.
    clear t s2 A0 C2.
Admitted.

Proposition subVar_id
            {B : Type}
            {C : Con B}
            {A : Ty B}
            {F : Type}
            {ar : F -> Ty B}
            (v : Var C A)
  : subVar v (idSub C ar) = TmVar v.
Proof.
  induction v.
  - reflexivity.
  - simpl ; cbn.
    admit.
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
Admitted.

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
    
Admitted.

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
