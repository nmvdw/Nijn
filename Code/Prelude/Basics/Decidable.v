Require Import Nijn.Prelude.Checks.
Require Import Nijn.Prelude.Funext.
Require Import Bool.

(** * Decidable propositions *)

(** A proposition is called decidable if we can either find an element of it or if we can refute it. As such, decidable propositions are those for which the law of excluded middle holds. *)
Inductive dec (A : Prop) : Type :=
| Yes : A -> dec A
| No : (A -> False) -> dec A.

Arguments Yes {_} _.
Arguments No {_} _.

(** * Examples of decidable propositions *)
Definition dec_True : dec True := Yes I.

Definition dec_False : dec False := No (fun z => z).

Definition dec_not {A : Prop} (x : dec A) : dec (~A)
  := match x with
     | Yes a => No (fun q => q a)
     | No a => Yes a
     end.

Definition dec_and {A B : Prop} (x : dec A) (y : dec B) : dec (A /\ B)
  := match x , y with
     | Yes p , Yes q => Yes (conj p q)
     | No p , _ => No (fun z => p (proj1 z))
     | _ , No q => No (fun z => q (proj2 z))
     end.

Definition dec_or {A B : Prop} (x : dec A) (y : dec B) : dec (A \/ B)
  := match x , y with
     | No p , No q =>
       No (fun z =>
           match z with
           | or_introl a => p a
           | or_intror b => q b
           end)
     | Yes p , _ => Yes (or_introl p)
     | _ , Yes q => Yes (or_intror q)
     end.

(** * Decidable equality *)

Class decEq (A : Type) :=
  {
    dec_eq : forall (a₁ a₂ : A), dec (a₁ = a₂)
  }.

(** A tactic for proving decidable equality on finite types *)
Ltac decEq_finite :=
  unshelve esplit ;
  (let x := fresh in intro x ; induction x) ;
  (let x := fresh in intro x ; induction x) ;
  try (apply Yes ; abstract (reflexivity)) ;
  try (apply No ; abstract (discriminate)).

Notation "! p" := (eq_sym p) (at level 80).

(** We use the so-called `transport` function at numerous occassions. Our usage is more technical though. *)
Definition transport
           {A : Type}
           (Y : A -> Type)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : Y a₁ -> Y a₂
  := match p with
     | eq_refl => fun z => z
     end.

Lemma transport_sym_p
      {A : Type}
      (B : A -> Type)
      {x y : A}
      (p : x = y)
      (b : B x)
  : transport B (eq_sym p) (transport B p b) = b.
Proof.
  subst.
  cbn.
  reflexivity.
Qed.

(** If a type has decidable equality, then all proofs of equality are equal *)
Proposition path_in_sigma_fst
            {A : Type}
            {B : A -> Type}
            {x y : {x : A & B x}}
            (p : x = y)
  : projT1 x = projT1 y.
Proof.
  induction p.
  reflexivity.
Defined.

Proposition path_in_sigma_snd
            {A : Type}
            {B : A -> Type}
            {x y : {x : A & B x}}
            (p : x = y)
  : transport B (path_in_sigma_fst p) (projT2 x) = projT2 y.
Proof.
  subst.
  reflexivity.
Defined.

Proposition from_path_in_sigma
            {A : Type}
            (B : A -> Type)
            {a : A}
            {b1 b2 : B a}
            (p : existT _ a b1 = existT _ a b2)
  : b1 = b2.
Proof.
  pose (path_in_sigma_snd p) as q.
  rewrite (UIP (path_in_sigma_fst p) eq_refl) in q.
  exact q.
Defined.

(** * Examples of types with decidable equality *)

(** The unit type has decidable equality *)
Definition dec_eq_unit
           (x y : unit)
  : dec (x = y)
  := match x , y with
     | tt , tt => Yes eq_refl
     end.

Global Instance decEq_unit : decEq unit
  := {| dec_eq := dec_eq_unit |}.

(** The booleans have decidable equality *)
Definition dec_eq_bool
           (x y : bool)
  : dec (x = y)
  := match x , y with
     | true , true => Yes eq_refl
     | false , false => Yes eq_refl
     | true , false => No diff_true_false
     | false , true => No diff_false_true
     end.

Global Instance decEq_bool : decEq bool
  := {| dec_eq := dec_eq_bool |}.
  
(** The product of types with decidable equality has decidable equality *)
Section ProductDecEq.
  Context {A B : Type}
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
       | (x1 , x2) , (y1 , y2) =>
         match dec_eq x1 y1 with
         | Yes p =>
           match dec_eq x2 y2 with
           | Yes q => Yes (path_pair p q)
           | No q => No (fun (r : (x1 , x2) = (y1 , y2)) => q (f_equal snd r))
           end
         | No p => No (fun (r : (x1 , x2) = (y1 , y2)) => p (f_equal fst r))
         end
       end.

  Global Instance decEq_product : decEq (A * B)
    := {| dec_eq := dec_eq_product |}.
End ProductDecEq.

(** The sum of types with decidable equality has decidable equality *)
Section SumDecEq.
  Context {A B : Type}
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
         | Yes p => Yes (f_equal inl p)
         | No p => No (fun q => p (inl_inj q))
         end
       | inl x , inr y => No (fun q => inl_not_inr q)
       | inr x , inl y => No (fun q => inr_not_inl q)
       | inr x , inr y =>
         match dec_eq x y with
         | Yes p => Yes (f_equal inr p)
         | No p => No (fun q => p (inr_inj q))
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
         | 0 => Yes eq_refl
         | S m => No (fun (q : 0 = S m) => transport help_fam q I)
         end
     | S n =>
       fun m =>
         match m with
         | 0 => No (fun (q : S n = 0) => transport help_fam (!q) I)
         | S m =>
           match dec_eq_nat n m with
           | Yes p => Yes (f_equal S p)
           | No p => No (fun q => p (S_inj q))
           end
         end
     end.

Global Instance decEq_nat : decEq nat
  := {| dec_eq := dec_eq_nat |}.
