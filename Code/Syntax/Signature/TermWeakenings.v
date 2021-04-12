Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.

Inductive Wk {B : Type} : Con B -> Con B -> Type :=
| EmptyWk : Wk ∙ ∙
| Keep : forall {C1 C2 : Con B} (A : Ty B),
    Wk C1 C2 -> Wk (A ,, C1) (A ,, C2)
| Drop : forall {C1 C2 : Con B} (A : Ty B),
    Wk C1 C2 -> Wk (A ,, C1) C2.

Fixpoint idWk
         {B : Type}
         (C : Con B)
  : Wk C C
  := match C with
     | ∙ => EmptyWk
     | A ,, C => Keep A (idWk C)
     end.

Definition wkVar
           {B : Type}
           {C1 C2 : Con B}
           {A : Ty B}
           (v : Var C2 A)
           (w : Wk C1 C2)
  : Var C1 A.
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
         {C2 : Con B}
         {A : Ty B}
         {F : Type}
         {ar : F -> Ty B}
         (t : Tm ar C2 A)
  : forall {C1 : Con B}, Wk C1 C2 -> Tm ar C1 A
  := match t with
     | BaseTm f => fun _ _ => BaseTm f
     | TmVar v => fun _ w => TmVar (wkVar v w)
     | Lam f => fun _ w => Lam (wkTm f (Keep _ w))
     | App f t => fun _ w => App (wkTm f w) (wkTm t w) 
     end.
