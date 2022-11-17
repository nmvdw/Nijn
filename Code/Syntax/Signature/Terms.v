Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.Types.
Require Import Nijn.Syntax.Signature.Contexts.
Require Import Coq.Program.Equality.

Open Scope signature.

(** * Terms *)
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

Notation "'λ' x" := (Lam x) (at level 10) : signature.
Notation "f · x" := (App f x) (at level 20, left associativity) : signature.  

(** * Decidable alpha equality of terms *)
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

Definition tm_dec_eq_help
           {B : Type}
           {F : Type}
           `{decEq B}
           `{decEq F}
           {ar : F -> ty B}
           {C : con B}
           {A1 A2 : ty B}
           (t1 : tm ar C A1)
           (t2 : tm ar C A2)
           (p : A1 = A2)
  : dec (transport (tm ar C) p t1 = t2).
Proof.
  revert p.
  revert t2.
  revert A2.
  induction t1 ; intros ? t2 p.
  - (* t1 is a base term *)
    destruct t2.
    + (* t2 is a base term *)
      destruct (dec_eq f f0).
      * refine (Yes _).
        abstract
          (subst ;
           rewrite (hedberg p eq_refl) ;
           reflexivity).
      * refine (No _).
        abstract
          (intro q ;
           pose (transport
                   (is_BaseTm_at f)
                   q
                   (transport_BaseTm_at f (BaseTm f) p eq_refl))
             as r ;
           cbn in r ;
           contradiction).
    + (* t2 is a variable *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
    + (* t2 is a lambda abstraction *)
      refine (No _).
      abstract
        (intro q ; 
         exact (transport is_BaseTm q (transport_BaseTm (BaseTm f) p I))).
    + (* t2 is an application *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
  - (* t1 is a variable *)
    destruct t2.
    + (* t2 is a base term *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
    + (* t2 is a variable *)
      destruct (dec_eq (transport (var C) p v) v0).
      * refine (Yes _).
        abstract
          (subst ;
           reflexivity).
      * refine (No _).
        abstract
          (intro q ;
           subst ;
           simpl in * ;
           inversion q ;
           pose (path_in_sigma_uip _ H2) ;
           contradiction).
    + (* t2 is a lambda abstraction *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
    + (* t2 is an application *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
  - (* t1 is a lambda abstraction *)
    destruct t2.
    + (* t2 is a base term *)
      refine (No _).
      abstract
        (intro q ;
         refine ((transport is_Lambda q (transport_Lambda (λ t1) p I)))).
    + (* t2 is a variable *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
    + (* t2 is a lambda abstraction *)
      inversion p.
      induction H2.
      destruct (IHt1 _ t2 H3).
      * refine (Yes _).
        abstract
          (subst ; simpl ;
           rewrite (hedberg p eq_refl) ;
           reflexivity).
      * refine (No _).
        abstract
          (intro q ;
           subst ;
           simpl in * ;
           rewrite (hedberg p eq_refl) in q ;
           simpl in q ;
           inversion q; 
           pose (path_in_sigma_uip _ H2) as e ;
           pose (path_in_sigma_uip _ e) ;
           contradiction).
    + (* t2 is an application *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
  - (* t1 is an application *)
    destruct t2.
    + (* t2 is a base term *)
      refine (No _).
      abstract
        (subst ;
         simpl ;
         discriminate).
    + (* t2 is a variable *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
    + (* t2 is a lambda abstraction *)
      refine (No _).
      abstract
        (subst ;
         discriminate).
    + (* t2 is an application *)
      destruct (dec_eq A1 A0).
      * assert (pq : (A1 ⟶ A2) = (A0 ⟶ A3)).
        {
          subst.
          reflexivity.
        }
        destruct (IHt1_1 _ t2_1 pq) as [q | q], (IHt1_2 _ t2_2 e) as [n | n].
        ** refine (Yes _).
           abstract
             (subst ;
              rewrite (hedberg pq eq_refl) ;
              reflexivity).
        ** refine (No _).
           abstract
             (intro r ;
              subst ;
              simpl in * ;
              rewrite (hedberg pq eq_refl) in r ;
              simpl in r ;
              inversion r ;
              pose (path_in_sigma_uip _ H2) as e ;
              contradiction).
        ** refine (No _).
           abstract
             (intro r ;
              subst ;
              rewrite (hedberg pq eq_refl) in q ;
              simpl in * ;
              inversion r ;
              pose (path_in_sigma_uip _ H2) as e ;
              pose (path_in_sigma_uip _ e) ;
              contradiction).
        ** refine (No _).
           abstract
             (intro r ;
              subst ;
              rewrite (hedberg pq eq_refl) in q ;
              simpl in * ;
              inversion r ;
              pose (path_in_sigma_uip _ H3) ;
              contradiction).
      * refine (No _).
        abstract
          (intro q ;
           subst ;
           simpl in * ;
           inversion q ;
           contradiction).
Defined.

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
  := tm_dec_eq_help t1 t2 eq_refl.

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
