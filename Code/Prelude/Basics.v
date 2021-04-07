Require Import Coq.Logic.FunctionalExtensionality.

Inductive empty : Type := .

Inductive dec (A : Prop) : Type :=
| yes : A -> dec A
| no : ~A -> dec A.

Arguments yes {_} _.
Arguments no {_} _.

Class decEq (A : Type) :=
  {
    dec_eq : forall (a₁ a₂ : A), dec (a₁ = a₂)
  }.

Definition idpath
           {A : Type}
           {a : A}
  : a = a
  := eq_refl.

Definition sym
           {A : Type}
           {a b : A}
           (p : a = b)
  : b = a
  := match p with
     | eq_refl => eq_refl
     end.

Notation "! p" := (sym p) (at level 80).

Definition transport
           {A : Type}
           (Y : A -> Type)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : Y a₁ -> Y a₂
  := match p with
     | eq_refl => fun z => z
     end.

Definition ap
           {A B : Type}
           (f : A -> B)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : f a₁ = f a₂
  := match p with
     | eq_refl => eq_refl
     end.

(** The empty type has decidable equality *)
Definition dec_eq_empty
           (x y : empty)
  : dec (x = y)
  := match x with
     end.

Global Instance decEq_empty : decEq empty
  := {| dec_eq := dec_eq_empty |}.

(** The unit type has decidable equality *)
Definition dec_eq_unit
           (x y : unit)
  : dec (x = y)
  := match x , y with
     | tt , tt => yes idpath
     end.

Global Instance decEq_unit : decEq unit
  := {| dec_eq := dec_eq_unit |}.

(** The product of types with decidable equality has decidable equality *)
Section ProductDecEq.
  Context (A B : Type)
          `{decEq A}
          `{decEq B}.

  Definition path_pair
             {a₁ a₂ : A}
             {b₁ b₂ : B}
             (p : a₁ = a₂)
             (q : b₁ = b₂)
    : (a₁ , b₁) = (a₂ , b₂)
    := match p , q with
       | eq_refl , eq_refl => eq_refl
       end.

  Definition dec_eq_product
             (x y : A * B)
    : dec (x = y)
    := match x , y with
       | (x₁ , x₂) , (y₁ , y₂) =>
         match dec_eq x₁ y₁ with
         | yes p =>
           match dec_eq x₂ y₂ with
           | yes q => yes (path_pair p q)
           | no q => no (fun (r : (x₁ , x₂) = (y₁ , y₂)) => q (ap snd r))
           end
         | no p => no (fun (r : (x₁ , x₂) = (y₁ , y₂)) => p (ap fst r))
         end
       end.

  Global Instance decEq_product : decEq (A * B)
    := {| dec_eq := dec_eq_product |}.
End ProductDecEq.

(** The sum of types with decidable equality has decidable equality *)
Section SumDecEq.
  Context (A B : Type)
          `{decEq A}
          `{decEq B}.

  Definition inl_inj
             {x y : A}
             (p : (inl x : A + B) = inl y)
    : x = y.
  Proof.
    inversion p.
    reflexivity.
  Qed.

  Definition inr_inj
             {x y : B}
             (p : (inr x : A + B) = inr y)
    : x = y.
  Proof.
    inversion p.
    reflexivity.
  Qed.

  Definition inl_not_inr
             {x : A}
             {y : B}
             (p : inl x = inr y)
    : False.
  Proof.
    discriminate.
  Qed.

  Definition inr_not_inl
             {x : B}
             {y : A}
             (p : inr x = inl y)
    : False.
  Proof.
    discriminate.
  Qed.
  
  Definition dec_eq_sum
             (x y : A + B)
    : dec (x = y)
    := match x , y with
       | inl x , inl y =>
         match dec_eq x y with
         | yes p => yes (ap inl p)
         | no p => no (fun q => p (inl_inj q))
         end
       | inl x , inr y => no (fun q => inl_not_inr q)
       | inr x , inl y => no (fun q => inr_not_inl q)
       | inr x , inr y =>
         match dec_eq x y with
         | yes p => yes (ap inr p)
         | no p => no (fun q => p (inr_inj q))
         end
       end.

  Global Instance decEq_sum : decEq (A + B)
    := {| dec_eq := dec_eq_sum |}.
End SumDecEq.


(** The natural numbers have decidable equality *)
Definition help_fam
           (n : nat)
  : Prop
  := match n with
     | 0 => True
     | S _ => False
     end.

Definition S_inj
           {n m : nat}
           (p : S n = S m)
  : n = m.
Proof.
  inversion p.
  reflexivity.
Qed.

Fixpoint dec_eq_nat
         (n : nat)
  : forall (m : nat), dec (n = m)
  := match n with
     | 0 =>
       fun m =>
         match m with
         | 0 => yes idpath
         | S m => no (fun (q : 0 = S m) => transport help_fam q I)
         end
     | S n =>
       fun m =>
         match m with
         | 0 => no (fun (q : S n = 0) => transport help_fam (!q) I)
         | S m =>
           match dec_eq_nat n m with
           | yes p => yes (ap S p)
           | no p => no (fun q => p (S_inj q))
           end
         end
     end.

Global Instance decEq_nat : decEq nat
  := {| dec_eq := dec_eq_nat |}.

(** Abbreviation for functional extensionality *)
Definition funext
           {A : Type}
           {B : A -> Type}
           {f g : forall (a : A), B a}
           (p : forall (a : A), f a = g a)
  : f = g.
Proof.
  apply functional_extensionality_dep.
  exact p.
Qed.
  
