Require Import Nijn.Prelude.
Require Import Nijn.Syntax.Signature.Types.
Require Import Coq.Program.Equality.
Require Import List.
Require Import Lia.

(** * Contexts *)

(** A context is a list of types. We use them for typed variables. *)

(** Notational convention: contexts are denoted by [C1], [C2], ... *)

Inductive con (B : Type) : Type :=
| Empty : con B
| Extend : ty B -> con B -> con B.

Arguments Empty {_}.
Arguments Extend {_} _ _.

Notation "∙" := Empty : signature.
Notation "A ,, Γ" := (Extend A Γ) (at level 80, right associativity) : signature.

Fixpoint length_con
         {B : Type}
         (C : con B)
  : nat
  := match C with
     | ∙ => 0
     | _ ,, C => S(length_con C)
     end.

(** ** Decidable equality of contexts *)
Lemma not_empty_extend
      {B : Type}
      {A : ty B}
      {C : con B}
  : ~(∙ = (A ,, C)).
Proof.
  discriminate.
Qed.

Lemma not_extend_empty
      {B : Type}
      {A : ty B}
      {C : con B}
  : ~((A ,, C) = ∙).
Proof.
  discriminate.
Qed.

Lemma not_eq_extend_type
      {B : Type}
      {A₁ A₂ : ty B}
      {C₁ C₂ : con B}
      (p : ~(A₁ = A₂))
  : ~((A₁ ,, C₁) = (A₂ ,, C₂)).
Proof.
  intro q.
  inversion q.
  contradiction.
Qed.

Lemma not_eq_extend_con
      {B : Type}
      {A₁ A₂ : ty B}
      {C₁ C₂ : con B}
      (p : ~(C₁ = C₂))
  : ~((A₁ ,, C₁) = (A₂ ,, C₂)).
Proof.
  intro q.
  inversion q.
  contradiction.
Qed.

Lemma eq_extend
      {B : Type}
      {A₁ A₂ : ty B}
      {C₁ C₂ : con B}
      (p : A₁ = A₂)
      (q : C₁ = C₂)
  : (A₁ ,, C₁) = (A₂ ,, C₂).
Proof.
  subst.
  reflexivity.
Qed.

(** The function that decides equality of contexts *)
Fixpoint dec_eq_con
         {B : Type}
         `{decEq B}
         (C₁ C₂ : con B)
  : dec (C₁ = C₂)
  := match C₁ , C₂ with
     | ∙ , ∙ => Yes eq_refl
     | ∙ , _ ,, _ => No not_empty_extend
     | _ ,, _ , ∙ => No not_extend_empty
     | A₁ ,, C₁ , A₂ ,, C₂ =>
       match dec_eq A₁ A₂ with
       | No p => No (not_eq_extend_type p)
       | Yes p =>
         match dec_eq_con C₁ C₂ with
         | Yes q => Yes (eq_extend p q)
         | No q => No (not_eq_extend_con q)
         end
       end
     end.

Global Instance decEq_con {B : Type} `{decEq B} : decEq (con B) :=
  {| dec_eq := dec_eq_con |}.

(** * Variables *)

(** Note: we represent variables using De Bruijn indices *)
Inductive var {B : Type} : con B -> ty B -> Type :=
| Vz : forall {C : con B} {A : ty B},
    var (A ,, C) A
| Vs : forall {C : con B} {A1 A2 : ty B},
    var C A2 -> var (A1 ,, C) A2.

(** Every natural number gives rise to a variable if that number actually is a valid position in the list *)
Definition nat_to_var
           {B : Type}
           {C : con B}
           (n : nat)
           (Hn : n < length_con C)
  : { A : ty B & var C A }.
Proof.
  revert C Hn.
  induction n as [ | n IHn ] ; intros C Hn.
  - destruct C as [ | A C ].
    + abstract
        (cbn in * ;
         exfalso ;
         lia).
    + exists A.
      apply Vz.
  - destruct C as [ | A C ].
    + abstract
        (cbn in * ;
         exfalso ;
         lia).
    + cbn in Hn.
      assert (n < length_con C) as H' by lia.
      destruct (IHn C H') as [ A' v ].
      exists A'.
      exact (Vs v).
Defined.

(** ** Decidable equality of variables *)

(** We decide equality of variables by mapping them to the natural numbers and then deciding equality of the natural numbers. *)
Fixpoint var_to_nat
         {B : Type}
         {C : con B}
         {A : ty B}
         (v : var C A)
  : nat
  := match v with
     | Vz => 0
     | Vs v => S(var_to_nat v)
     end.

Proposition var_tonat_eq_ty
            {B : Type}
            {C : con B}
            {A1 A2 : ty B}
            {v1 : var C A1}
            {v2 : var C A2}
            (p : var_to_nat v1 = var_to_nat v2)
  : A1 = A2.
Proof.
  induction v1.
  - dependent destruction v2.
    + reflexivity.
    + cbn in p.
      discriminate.
  - dependent destruction v2.
    + simpl in p.
      discriminate.
    + f_equal.
      apply (IHv1 v2).
      simpl in p.
      inversion p.
      reflexivity.
Qed.

Proposition var_tonat_eq
            {B : Type}
            {C : con B}
            {A : ty B}
            {v1 v2 : var C A}
            (p : var_to_nat v1 = var_to_nat v2)
  : v1 = v2.
Proof.
  induction v1.
  - dependent destruction v2.
    + reflexivity.
    + cbn in p.
      discriminate.
  - dependent destruction v2.
    + simpl in p.
      discriminate.
    + f_equal.
      apply IHv1.
      simpl in p.
      inversion p.
      reflexivity.
Qed.

Definition dec_eq_Var
        {B : Type}
        {C : con B}
        {A : ty B}
        (v1 v2 : var C A)
  : dec (v1 = v2)
  := match dec_eq (var_to_nat v1) (var_to_nat v2) with
     | Yes p => Yes (var_tonat_eq p)
     | No p => No (fun q => p (f_equal _ q))
     end.

Global Instance decEq_Var
       {B : Type}
       {C : con B}
       {A : ty B}
  : decEq (var C A)
  := {| dec_eq := dec_eq_Var |}.

(** * The type of variables is finite *)
Fixpoint all_Vars
         {B : Type}
         `{decEq B}
         (C : con B)
  : forall (A : ty B), list (var C A)
  := match C with
     | ∙ => fun _ => nil
     | A1 ,, C =>
       fun A2 =>
         match dec_eq A1 A2 with
         | Yes p => transport (var _) p Vz :: map Vs (all_Vars C A2)
         | No p => map Vs (all_Vars C A2)
         end
     end.

Global Instance isFinite_var
       {B : Type}
       `{decEq B}
       (C : con B)
       (A : ty B)
  : isFinite (var C A).
Proof.
  simple refine {| els := all_Vars C A ; allIsMember := _ |}.
  intro v.
  dependent induction v.
  - simpl.
    destruct (dec_eq_Ty A A) ; try contradiction.
    rewrite (UIP e eq_refl).
    simpl.
    left.
    reflexivity.
  - simpl ; destruct (dec_eq_Ty A1 A2).
    + simpl.
      subst.
      right.
      apply in_map.
      apply IHv.
    + simpl.
      apply in_map.
      apply IHv.
Defined.
