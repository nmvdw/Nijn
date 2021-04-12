Require Import Syntax.Signature.Types.
Require Import Syntax.Signature.Contexts.
Require Import Syntax.Signature.Terms.

Definition TODO {A : Type} : A.
Admitted.

Fixpoint wkTm
         {B : Type} 
         {C : Con B}
         {F : Type}
         {ar : F -> Ty B}
         {A1 A2 : Ty B}
         (t : Tm ar C A1)
  : Tm ar (A2 ,, C) A1
  := match t with
     | BaseTm f => BaseTm f
     | TmVar v => TmVar (Vs v)
     | Lam f => Lam _
     | App f t => App (wkTm f) (wkTm t)
     end.
  := Vs v.


         {F : Type}
         {ar : F -> Ty B}
         (t : Tm ar Γ₂ A)
  : forall {Γ₁ : Con B}, Wk Γ₁ Γ₂ -> Tm ar Γ₁ A
  := match t with
     | BaseTm f => fun _ _ => BaseTm f
     | TmVar v => fun _ w => TmVar (wkVar w v)
     | Lam f => fun _ w => Lam (wkTm f (Keep _ w))
     | App f t => fun _ w => App (wkTm f w) (wkTm t w) 
     end.




Inductive Wk {B : Type} : Con B -> Con B -> Type :=
| EmptyWk : Wk ∙ ∙
| Keep : forall {Γ₁ Γ₂ : Con B} (A : Ty B),
    Wk Γ₁ Γ₂ -> Wk (A ,, Γ₁) (A ,, Γ₂)
| Drop : forall {Γ₁ Γ₂ : Con B} (A : Ty B),
    Wk Γ₁ Γ₂ -> Wk (A ,, Γ₁) Γ₂.

Fixpoint idWk
         {B : Type}
         (Γ : Con B)
  : Wk Γ Γ
  := match Γ with
     | ∙ => EmptyWk
     | A ,, Γ => Keep A (idWk Γ)
     end.

Definition TODO {A : Type} : A.
Admitted.


Require Import Equations.Equations.

Derive NoConfusion for Con.
Derive Signature for Var.

Equations wkVar
          {B : Type}
          {Γ₂ : Con B}
          {Γ₁ : Con B}
          {A : Ty B}
          (v : Var Γ₂ A)
          (w : Wk Γ₁ Γ₂)
  : Var Γ₁ A
  := wkVar v (Drop A w) => Vs (wkVar v w) ;
     wkVar Vz (Keep A w) => Vz ;
     wkVar (Vs v) (Keep A w) => Vs (wkVar v w).

Require Import Extraction.
Recursive Extraction wkVar.


Fixpoint wkVar
         {B : Type}
         {Γ₁ Γ₂ : Con B}
         (w : Wk Γ₁ Γ₂)
  : forall {A : Ty B}, Var Γ₂ A -> Var Γ₁ A
  := match w with
     | EmptyWk => fun _ v => v
     | @Drop _ C1 C2 A' w => fun A v => Vs (wkVar w v)
     | @Keep _ C1 C2 A' w =>
       fun A v =>
                    (*
         match v in Var (A' ,, Γ) A with
         | Vz => Vz
         | Vs v => _
         end
                     *)
       (*
       fun A v => 
         (fun Γ =>
            match v in Var (A' ,, Γ) _ return Var Γ _ with
            | Vz => _
            | Vs v => Vs (wkVar w _)
            end)
           C2
        *)
     end.

Require Import Extraction.
Extraction Language Haskell.
Extraction wkVar.

Fixpoint wkTm
         {B : Type}
         {Γ₂ : Con B}
         {A : Ty B}
         {F : Type}
         {ar : F -> Ty B}
         (t : Tm ar Γ₂ A)
  : forall {Γ₁ : Con B}, Wk Γ₁ Γ₂ -> Tm ar Γ₁ A
  := match t with
     | BaseTm f => fun _ _ => BaseTm f
     | TmVar v => fun _ w => TmVar (wkVar w v)
     | Lam f => fun _ w => Lam (wkTm f (Keep _ w))
     | App f t => fun _ w => App (wkTm f w) (wkTm t w) 
     end.


Extraction Language Haskell.
Extraction wkTm.
