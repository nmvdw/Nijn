Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.Types.
Require Import Nijn.Syntax.Signature.Contexts.
Require Import Coq.Program.Equality.

Open Scope signature.

(** * Terms *)

(** Notational contention: we write [F] for the type of function symbols and [ar] for their arities. We denote terms by [t1] and [t2] and we use [f1], [f2], ... for function symbols and terms of a function type. *)
Inductive tm {B : Type} {F : Type} (ar : F -> ty B) (C : con B) : ty B -> Type :=
| BaseTm : forall (f : F),
    tm ar C (ar f)
| TmVar : forall {A : ty B},
    var C A -> tm ar C A
| Lam : forall {A1 A2 : ty B},
    tm ar (A1 ,, C) A2 -> tm ar C (A1 ⟶ A2)
| App : forall {A1 A2 : ty B},
    tm ar C (A1 ⟶ A2) -> tm ar C A1 -> tm ar C A2.

Arguments BaseTm {_} {_} {_} {_} _.
Arguments TmVar {_} {_} {_} {_} {_} _.
Arguments Lam {_} {_} {_} {_} {_} {_} _.
Arguments App {_} {_} {_} {_} {_} {_} _ _.

Notation "'λ' x" := (Lam x) (at level 21) : signature.
Notation "f · x" := (App f x) (at level 20, left associativity) : signature.

(** The following two definitions are used so that we can denote De Bruijn indices using natural numbers. *)
Record tm_with_ty
       {B : Type}
       {F : Type}
       (ar : F -> ty B)
       (C : con B)
  : Type
  := { type : ty B ; term :> tm ar C type }.    

Definition v_idx
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           (n : nat)
           (Hn : n < length_con C)
  : tm_with_ty ar C.
Proof.
  destruct (nat_to_var n Hn) as [ A v ].
  exact {| type := A ; term := TmVar v |}.
Defined.

Notation "'V' n" := (v_idx n _) (at level 0).

(** ** Decidable alpha equality of terms *)

(** To decide equality of terms, we first map them to untyped terms. After that, we decide equality of untyped terms. *)
Inductive ut_tm (B : Type) (F : Type) : Type :=
| UBaseTm : F -> ut_tm B F
| UTmVar : nat -> ut_tm B F
| ULam : ty B -> ut_tm B F -> ut_tm B F
| UApp : ut_tm B F -> ut_tm B F -> ut_tm B F.

Arguments UBaseTm {B F} f.
Arguments UTmVar {B F} n.
Arguments ULam {B F} A f.
Arguments UApp {B F} f t.

Program Fixpoint dec_eq_ut_tm
                 {B : Type}
                 {F : Type}
                 `{decEq B}
                 `{decEq F}
                 (t₁ t₂ : ut_tm B F)
  : dec (t₁ = t₂)
  := match t₁ , t₂ with
     | UBaseTm f₁ , UBaseTm f₂ =>
       match dec_eq f₁ f₂ with
       | Yes _ => Yes _
       | No _ => No _
       end
     | UBaseTm f₁ , UTmVar n₂ => No _
     | UBaseTm f₁ , ULam A₂ f₂ => No _
     | UBaseTm f₁ , UApp f₂ t₂ => No _
     | UTmVar n₁ , UBaseTm f₂ => No _
     | UTmVar n₁ , UTmVar n₂ =>
       match dec_eq n₁ n₂ with
       | Yes _ => Yes _
       | No _ => No _
       end
     | UTmVar n₁ , ULam A₂ f₂ => No _
     | UTmVar n₁ , UApp f₂ t₂ => No _
     | ULam A₁ f₁ , UBaseTm f₂ => No _
     | ULam A₁ f₁ , UTmVar n₂ => No _
     | ULam A₁ f₁ , ULam A₂ f₂ =>
       match dec_eq A₁ A₂ , dec_eq_ut_tm f₁ f₂ with
       | Yes _ , Yes _ => Yes _
       | _ , No _ => No _
       | No _ , _ => No _
       end
     | ULam A₁ f₁ , UApp f₂ t₂ => No _
     | UApp f₁ t₁ , UBaseTm f₂ => No _
     | UApp f₁ t₁ , UTmVar n₂ => No _
     | UApp f₁ t₁ , ULam A₂ f₂ => No _
     | UApp f₁ t₁ , UApp f₂ t₂ =>
       match dec_eq_ut_tm f₁ f₂ , dec_eq_ut_tm t₁ t₂ with
       | Yes _ , Yes _ => Yes _
       | _ , No _ => No _
       | No _ , _ => No _
       end
     end.

Global Instance ut_tm_decEq
       {B : Type}
       {F : Type}
       `{decEq B}
       `{decEq F}
  : decEq (ut_tm B F)
  := {| dec_eq := dec_eq_ut_tm |}.

Fixpoint tm_to_ut_tm
         {B : Type}
         {F : Type}
         {ar : F -> ty B}
         {C : con B}
         {A : ty B}
         (t : tm ar C A)
  : ut_tm B F
  := match t with
     | BaseTm f => UBaseTm f
     | TmVar v => UTmVar (var_to_nat v)
     | @Lam _ _ _ _ A1 A2 f => ULam A1 (tm_to_ut_tm f)
     | App f t => UApp (tm_to_ut_tm f) (tm_to_ut_tm t)
     end.

Proposition eq_ut_tm_ty
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            {t1 : tm ar C A1}
            {t2 : tm ar C A2}
            (p : tm_to_ut_tm t1 = tm_to_ut_tm t2)
  : A1 = A2.
Proof.
  revert A2 t2 p.
  induction t1 ;
    intros ? t2 ;
    destruct t2 ;
    intros p ;
    inversion p ;
    subst.
  - reflexivity.
  - apply (var_tonat_eq_ty H0).
  - f_equal.
    apply (IHt1 _ t2).
    assumption.
  - pose (IHt1_1 _ t2_1 H0) as q.
    inversion q.
    reflexivity.
Qed.

Proposition eq_ut_tm
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            {t1 : tm ar C A1}
            {t2 : tm ar C A2}
            (p : tm_to_ut_tm t1 = tm_to_ut_tm t2)
            (q : A1 = A2)
  : transport (tm ar C) q t1 = t2.
Proof.
  revert A2 t2 p q.
  induction t1 ;
    intros ? t2 ;
    destruct t2 ;
    intros p q ;
    inversion p ;
    subst.
  - rewrite (UIP q (eq_refl _)).
    reflexivity.
  - cbn.
    f_equal.
    apply var_tonat_eq.
    assumption.
  - inversion q.
    subst.
    rewrite (UIP q (eq_refl _)) ; cbn.
    f_equal.
    refine (IHt1 _ t2 _ (eq_refl _)).
    assumption.
  - cbn.
    assert (A0 = A1).
    {
      symmetry.
      apply (eq_ut_tm_ty H1).
    }
    subst.
    rewrite <- (IHt1_1 _ t2_1 H0 (eq_refl _)) ; cbn.
    f_equal.
    apply (IHt1_2 _ t2_2 H1 (eq_refl _)).
Qed.

Definition tm_dec_eq
           {B : Type}
           {F : Type}
           `{decEq B}
           `{decEq F}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t1 : tm ar C A)
           (t2 : tm ar C A)
  : dec (t1 = t2)
  := match dec_eq_ut_tm (tm_to_ut_tm t1) (tm_to_ut_tm t2) with
     | Yes p => Yes (eq_ut_tm p (eq_refl _))
     | No q => No (fun n => q (f_equal _ n))
     end.

Global Instance tm_decEq
       {B : Type}
       {F : Type}
       `{decEq B}
       `{decEq F}
       (ar : F -> ty B)
       (C : con B)
       (A : ty B)
  : decEq (tm ar C A)
  := {| dec_eq := tm_dec_eq |}.

Definition is_BaseTm
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : Prop
  := match t with
     | BaseTm _ => True
     | _ => False
     end.

Definition transport_BaseTm
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (t : tm ar C A1)
           (p : A1 = A2)
           (Ht : is_BaseTm t)
  : is_BaseTm (transport (tm ar C) p t).
Proof.
  subst.
  simpl.
  exact Ht.
Qed.

Lemma is_BaseTm_transport
      {B : Type}
      {F : Type}
      {ar : F -> ty B}
      {C : con B}
      {A1 A2 : ty B}
      (p : A1 = A2)
      (t : tm ar C A1)
  : is_BaseTm (transport _ p t) -> is_BaseTm t.
Proof.
  subst.
  exact (fun x => x).
Qed.

Definition is_BaseTm_at
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (f : F)
           (t : tm ar C A)
  : Prop
  := match t with
     | BaseTm f' => f = f'
     | _ => False
     end.

Definition transport_BaseTm_at
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (f : F)
           (t : tm ar C A1)
           (p : A1 = A2)
           (Ht : is_BaseTm_at f t)
  : is_BaseTm_at f (transport (tm ar C) p t).
Proof.
  subst.
  simpl.
  exact Ht.
Qed.

Definition is_TmVar
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : Prop
  := match t with
     | TmVar _ => True
     | _ => False
     end.

Definition is_Lambda
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (t : tm ar C A)
  : Prop
  := match t with
     | λ _ => True
     | _ => False
     end.

Definition transport_Lambda
           {B : Type}
           {F : Type}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (t : tm ar C A1)
           (p : A1 = A2)
           (Ht : is_Lambda t)
  : is_Lambda (transport (tm ar C) p t).
Proof.
  subst.
  simpl.
  exact Ht.
Qed.

(** ** Equality principles for terms *)
Proposition App_eq_Ty
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A1' A2 : ty B}
            {f : tm ar C (A1 ⟶ A2)}
            {f' : tm ar C (A1' ⟶ A2)}
            {t : tm ar C A1}
            {t' : tm ar C A1'}
            (p : f · t = f' · t')
  : A1 = A1'.
Proof.
  inversion p.
  reflexivity.
Defined.

Proposition App_eq_fst
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A1' A2 : ty B}
            {f : tm ar C (A1 ⟶ A2)}
            {f' : tm ar C (A1' ⟶ A2)}
            {t : tm ar C A1}
            {t' : tm ar C A1'}
            (p : f · t = f' · t')
  : transport (fun A => tm ar C (A ⟶ A2)) (App_eq_Ty p) f = f'.
Proof.
  dependent destruction p.
  reflexivity.
Defined.

Proposition App_eq_snd
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A1' A2 : ty B}
            {f : tm ar C (A1 ⟶ A2)}
            {f' : tm ar C (A1' ⟶ A2)}
            {t : tm ar C A1}
            {t' : tm ar C A1'}
            (p : f · t = f' · t')
  : transport (tm ar C) (App_eq_Ty p) t = t'.
Proof.
  dependent destruction p.
  reflexivity.
Defined.

Proposition Lam_eq'
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A1' A2 : ty B}
            {f : tm ar (A1 ,, C) A2}
            {f' : tm ar (A1' ,, C) A2}
            (p : A1 = A1')
            (q : λ (transport (fun Z => tm ar (Z ,, C) A2) p f) = λ f')
  : transport (fun Z => tm ar (Z ,, C) A2) p f = f'.
Proof.
  dependent destruction q.
  reflexivity.
Defined.

Proposition Lam_eq
            {B : Type}
            {F : Type}
            {ar : F -> ty B}
            {C : con B}
            {A1 A2 : ty B}
            {f f' : tm ar (A1 ,, C) A2}
            (p : λ f = λ f')
  : f = f'.
Proof.
  exact (Lam_eq' eq_refl p).
Defined.
