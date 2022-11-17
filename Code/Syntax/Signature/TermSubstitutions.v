Require Import Nijn.Syntax.Signature.Types.
Require Import Nijn.Syntax.Signature.Contexts.
Require Import Nijn.Syntax.Signature.Terms.
Require Import Nijn.Syntax.Signature.TermWeakenings.

(** * Substitutions *)

Inductive sub {B : Type} {F : Type} (ar : F -> ty B) : con B -> con B -> Type :=
| ToEmpty : forall (C : con B), sub ar C ∙
| ExtendSub : forall {C1 C2 : con B} {A : ty B},
    sub ar C1 C2 -> tm ar C1 A -> sub ar C1 (A ,, C2).

Arguments ToEmpty {B F ar} C.
Arguments ExtendSub {B F ar C1 C2 A}.
Notation "s && t" := (ExtendSub s t).

(** * Operations on substitutions *)

(** Dropping a variable *)
Fixpoint dropSub
         {B : Type}
         {C1 C2 : con B}
         {F : Type}
         {ar : F -> ty B}
         (A : ty B)
         (s : sub ar C1 C2)
  : sub ar (A ,, C1) C2
  := match s with
     | ToEmpty _ => ToEmpty _
     | s && t => dropSub A s && wkTm t (Drop A (idWk _))
     end.

(** Keeping a variable *)
Definition keepSub
           {B : Type}
           {C1 C2 : con B}
           {F : Type}
           {ar : F -> ty B}
           (A : ty B)
           (s : sub ar C1 C2)
  : sub ar (A ,, C1) (A ,, C2)
  := dropSub A s && TmVar Vz.

(** Identity *)
Fixpoint idSub
         {B : Type}
         (C : con B)
         {F : Type}
         (ar : F -> ty B)
  : sub ar C C
  := match C with
     | ∙ => ToEmpty _
     | A ,, C => dropSub A (idSub C ar) && TmVar Vz
     end.

(** Each weakening is a substitution *)
Fixpoint wkToSub
         {B : Type}
         {C1 C2 : con B}
         {F : Type}
         {ar : F -> ty B}
         (w : wk C1 C2)
  : sub ar C1 C2
  := match w with
     | EmptyWk => ToEmpty ∙
     | Keep A w => keepSub A (wkToSub w)
     | Drop A w => dropSub A (wkToSub w)
     end.

(** * Action of substitution on terms *)
Definition subVar
           {B : Type}
           {C1 C2 : con B}
           {F : Type}
           {ar : F -> ty B}
           {A : ty B}
           (v : var C2 A)
           (s : sub ar C1 C2)
  : tm ar C1 A.
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
         {C2 : con B}
         {A : ty B}
         {F : Type}
         {ar : F -> ty B}
         (t : tm ar C2 A)
  : forall {C1 : con B}, sub ar C1 C2 -> tm ar C1 A
  := match t with
     | BaseTm f => fun _ _ => BaseTm f
     | TmVar v => fun _ s => subVar v s
     | Lam f => fun _ s => Lam (subTm f (keepSub _ s))
     | App f t => fun _ s => App (subTm f s) (subTm t s) 
     end.

Notation "t [ s ]" := (subTm t s) (at level 20).

(** Composition of substitutions *)
Definition compSub
           {B : Type}
           {C1 C2 C3 : con B}
           {F : Type}
           {ar : F -> ty B}
           (s2 : sub ar C2 C3)
           (s1 : sub ar C1 C2)
  : sub ar C1 C3.
Proof.
  induction s2 as [ | ? ? ? s2 IHs2 t ].
  - apply ToEmpty.
  - exact (IHs2 s1 && t [ s1 ]).
Defined.
