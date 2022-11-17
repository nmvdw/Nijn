Require Import Nijn.Syntax.Signature.Types.
Require Import Nijn.Syntax.Signature.Contexts.
Require Import Nijn.Syntax.Signature.Terms.

(** * Weakenings of contexts *)

(** The type of weakenings *)
Inductive wk {B : Type} : con B -> con B -> Type :=
| EmptyWk : wk ∙ ∙
| Keep : forall {C1 C2 : con B} (A : ty B),
    wk C1 C2 -> wk (A ,, C1) (A ,, C2)
| Drop : forall {C1 C2 : con B} (A : ty B),
    wk C1 C2 -> wk (A ,, C1) C2.

(** * Operations on weakenings *)

(** Identity weakening *)
Fixpoint idWk
         {B : Type}
         (C : con B)
  : wk C C
  := match C with
     | ∙ => EmptyWk
     | A ,, C => Keep A (idWk C)
     end.

(** Composition of weakenings *)
Definition compWk
           {B : Type}
           {C1 C2 C3 : con B}
           (w1 : wk C2 C3)
           (w2 : wk C1 C2)
  : wk C1 C3.
Proof.
  revert w1.
  revert C3.
  induction w2 as [ | C1 C2 A w2 IHw2 | C1 C2 A w2 IHw2 ] ; intros C3 w1.
  - exact w1.
  - inversion w1.
    + apply Keep.
      apply IHw2.
      exact X.
    + apply Drop.
      apply IHw2.
      exact X.
  - exact (Drop A (IHw2 _ w1)).
Defined.

(** Substitution along weakenings *)
Definition wkVar
           {B : Type}
           {C1 C2 : con B}
           {A : ty B}
           (v : var C2 A)
           (w : wk C1 C2)
  : var C1 A.
Proof.
  induction w.
  - exact v.
  - inversion v as [ | ? ? ? v' ].
    + exact Vz.
    + exact (Vs (IHw v')).
  - exact (Vs (IHw v)).
Defined.

Fixpoint wkTm
         {B : Type}
         {C2 : con B}
         {A : ty B}
         {F : Type}
         {ar : F -> ty B}
         (t : tm ar C2 A)
  : forall {C1 : con B}, wk C1 C2 -> tm ar C1 A
  := match t with
     | BaseTm f => fun _ _ => BaseTm f
     | TmVar v => fun _ w => TmVar (wkVar v w)
     | Lam f => fun _ w => Lam (wkTm f (Keep _ w))
     | App f t => fun _ w => App (wkTm f w) (wkTm t w) 
     end.
