Require Import Prelude.Funext.
Require Import List.
Require Import Bool.
Require Import String.
Require Import Coq.Program.Equality.
Require Import Lia.

(** Useful lemma *)
Proposition plus_ge
            {n1 n2 m1 m2 : nat}
            (p : n1 >= n2)
            (q : m1 >= m2)
  : n1 + m1 >= n2 + m2.
Proof.
  nia.
Qed.

(** * Basics functions *)

Arguments id {_} _/.

Definition comp
           {X Y Z : Type}
           (g : Y -> Z)
           (f : X -> Y)
           (x : X)
  : Z
  := g(f x).

Notation "g 'o' f" := (comp g f) (at level 40, left associativity).
Arguments comp {_ _ _} _ _ _/.

Definition option_bind
           {A B : Type}
           (x : option A)
           (f : A -> option B)
  : option B
  := match x with
     | Some a => f a
     | None => None
     end.

Notation "x >>= f" := (option_bind x f) (at level 70).

Fixpoint list_option
         {A : Type}
         (l : list (option A))
  : option (list A)
  := match l with
     | nil => Some nil
     | x :: xs =>
       list_option xs >>= fun ys => x >>= fun y => Some (y :: ys)
     end.

(** * Decidable propositions *)
Inductive dec (A : Prop) : Type :=
| Yes : A -> dec A
| No : (A -> False) -> dec A.

Arguments Yes {_} _.
Arguments No {_} _.

(** * Decidable equality *)

Class decEq (A : Type) :=
  {
    dec_eq : forall (a₁ a₂ : A), dec (a₁ = a₂)
  }.

Notation "! p" := (eq_sym p) (at level 80).

Definition transport
           {A : Type}
           (Y : A -> Type)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
  : Y a₁ -> Y a₂
  := match p with
     | eq_refl => fun z => z
     end.

(* begin hide *)
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
(* end hide *)

(** If a type has decidable equality, then all proofs of equality are equal *)
Definition hedberg_map
           {A : Type}
           `{decEq A}
           {a1 a2 : A}
           (p : a1 = a2)
  : a1 = a2
  := match dec_eq a1 a2 with
     | Yes q => q
     | No _ => p
     end.

Lemma hedberg_const
      {A : Type}
      `{decEq A}
      {a1 a2 : A}
      (p1 p2 : a1 = a2)
  : hedberg_map p1 = hedberg_map p2.
Proof.
  unfold hedberg_map.
  destruct (dec_eq a1 a2) as [r | r].
  - reflexivity.
  - contradiction.
Qed.

Lemma hedberg_formula
      {A : Type}
      `{decEq A}
      {a1 a2 : A}
      (p : a1 = a2)
  : p = eq_trans (! (hedberg_map eq_refl)) (hedberg_map p).
Proof.
  unfold hedberg_map.
  subst.
  destruct (dec_eq a2 a2).
  - rewrite eq_trans_sym_inv_l.
    reflexivity.
  - reflexivity.
Qed.

Theorem hedberg
        {A : Type}
        `{decEq A}
        {a1 a2 : A}
        (p q : a1 = a2)
  : p = q.
Proof.
  etransitivity.
  {
    apply hedberg_formula.
  }
  rewrite (hedberg_const p q).
  symmetry.
  apply hedberg_formula.
Qed.

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

Proposition path_in_sigma_uip
            {A : Type}
            `{decEq A}
            (B : A -> Type)
            {a : A}
            {b1 b2 : B a}
            (p : existT _ a b1 = existT _ a b2)
  : b1 = b2.
Proof.
  pose (path_in_sigma_snd p) as q.
  rewrite (hedberg (path_in_sigma_fst p) eq_refl) in q.
  exact q.
Defined.

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

  (* begin hide *)
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
  (* end hide *)
  
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
(* begin hide *)
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
(* end hide *)

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

(** Strings have decidable equality *)
Definition dec_eq_string
           (s1 s2 : string)
  : dec (s1 = s2)
  := match string_dec s1 s2 with
     | left p => Yes p
     | right p => No p
     end.

Global Instance decEq_string : decEq string
  := {| dec_eq := dec_eq_string |}.

(** * Finite types *)
Inductive isMember {A : Type} : A -> list A -> Type :=
| Here : forall (a : A) (xs : list A), isMember a (a :: xs)
| There : forall {a : A} (x : A) {xs : list A},
    isMember a xs -> isMember a (x :: xs).

Notation "a ∈ l" := (isMember a l) (at level 60).

Definition here_eq
           {A : Type}
           {a1 a2 : A}
           (p : a2 = a1)
           (l : list A)
  : a1 ∈ (a2 :: l).
Proof.
  induction p.
  apply Here.
Defined.

Definition in_tail
           {A : Type}
           {a x : A}
           {xs : list A}
           (p : In a (x :: xs))
           (q : a <> x)
  : In a xs.
Proof.
  simpl in p.
  destruct p as [p | p].
  - contradiction (q (! p)).
  - exact p.
Qed.

Fixpoint in_to_isMember
         {A : Type}
         `{decEq A}
         {a : A}
         {l : list A}
  : In a l -> isMember a l
  := match l with
     | nil => fun p => False_rect _ p
     | x :: xs =>
       fun p =>
         match dec_eq a x with
         | Yes e => here_eq (eq_sym e) _
         | No e => There _ (in_to_isMember (in_tail p e))
         end
     end.

Definition isMember_to_in
           {A : Type}
           {a : A}
           {l : list A}
           (p : isMember a l)
  : In a l.
Proof.
  induction p.
  - apply in_eq.
  - apply in_cons.
    apply IHp.
Qed.

Definition isMember_append_left
           {A : Type}
           {a : A}
           {l1 : list A}
           (p : a ∈ l1)
           (l2 : list A)
  : a ∈ (l1 ++ l2).
Proof.
  induction p as [ x xs | x x' xs p IHp ] ; simpl.
  - apply Here.
  - apply There.
    apply IHp.
Defined.

Definition isMember_append_right
           {A : Type}
           {a : A}
           (l1 : list A)
           {l2 : list A}
           (p : a ∈ l2)
  : a ∈ (l1 ++ l2).
Proof.
  revert l2 p.
  induction l1 as [ | ? l IHl ] ; intros l2 p ; simpl.
  - exact p.
  - apply There.
    apply IHl.
    exact p.
Defined.

Definition isMember_map
           {A B : Type}
           {a : A}
           {l : list A}
           (f : A -> B)
           (p : a ∈ l)
  : f a ∈ map f l.
Proof.
  induction p as [ x xs | x x' xs p IHp ] ; simpl.
  - apply Here.
  - apply There.
    exact IHp.
Defined.

Class isFinite (A : Type) :=
  {
    els : list A ;
    allIsMember : forall (a : A), In a els
  }.

(** The unit type is finite *)
Global Instance isFinite_unit : isFinite unit.
Proof.
  simple refine {| els := tt :: nil ; allIsMember := _ |}.
  intro x.
  induction x.
  left.
  reflexivity.
Defined.

(** THe booleans are finite *)
Global Instance isFinite_bool : isFinite bool.
Proof.
  simple refine {| els := true :: false :: nil ; allIsMember := _ |}.
  intros [ | ].
  - left.
    reflexivity.
  - right ; left.
    reflexivity.
Defined.

(** The product of finite types is again finite *)
Fixpoint pairs
         {A B : Type}
         (l1 : list A)
         (l2 : list B)
  : list (A * B)
  := match l1 with
     | nil => nil
     | (x :: xs) => map (fun b => (x , b)) l2 ++ (pairs xs l2)
     end.

Proposition in_pairs
            {A B : Type}
            (l1 : list A)
            (l2 : list B)
            (a : A) (b : B)
            (Ha : In a l1)
            (Hb : In b l2)
  : In (a , b) (pairs l1 l2).
Proof.
  induction l1 as [ | x xs IHl ] ; simpl.
  - inversion Ha.
  - destruct Ha.
    + apply in_or_app.
      left ; subst.
      apply in_map.
      exact Hb.
    + apply in_or_app.
      right.
      apply IHl.
      exact H.
Qed.

Global Instance isFinite_prod
       {A B : Type}
       `{isFinite A}
       `{isFinite B}
  : isFinite (A * B).
Proof.
  simple refine {| els := pairs els els ; allIsMember := _ |}.
  intros [a b].
  apply in_pairs.
  - apply allIsMember.
  - apply allIsMember.
Defined.

(** The coproduct of finite types is finite *)
Global Instance isFinite_sum
       {A B : Type}
       `{isFinite A}
       `{isFinite B}
  : isFinite (A + B).
Proof.
  simple refine {| els := map inl els ++ map inr els ;
                   allIsMember := _ |}.
  intros [a | b].
  - apply in_or_app.
    left.
    apply in_map.
    apply allIsMember.
  - apply in_or_app.
    right.
    apply in_map.
    apply allIsMember.
Defined.

(** If we have a list, then the type of elements of that list is finite *)
Inductive members {A : Type} (l : list A) : Type :=
| MakeMem : forall (x : A), In x l -> members l.

Arguments MakeMem {_ _} _ _.

Definition member_el
           {A : Type}
           {l : list A}
           (x : members l)
  : A
  := match x with
     | MakeMem a _ => a
     end.

Definition member_isEl
           {A : Type}
           {l : list A}
           (x : members l)
  : In (member_el x) l
  := match x with
     | MakeMem a p => p
     end.

Program Fixpoint els_members
         {A : Type}
         (el_A : list A)
         (l : list A)
  : (forall (a : A), In a l -> In a el_A) -> list (members el_A) 
  := match l with
     | nil => fun p => nil
     | x :: xs =>
       fun p =>
         MakeMem x (p _ _) :: els_members el_A xs (fun a z => (p a _))
     end.

Definition A_to_member
           {A : Type}
           (el_A : list A)
           (l : list A)
           (p : forall (a : A), In a l -> In a el_A)
           (a : A)
           (Ha : In a l)
  : members el_A
  := MakeMem a (p _ Ha).

Proposition in_els_members
            {A : Type}
            (el_A : list A)
            (l : list A)
            (p : forall (a : A), In a l -> In a el_A)
            (a : A)
            (Ha : In a l)
  : In (A_to_member el_A l p a Ha) (els_members el_A l p).
Proof.
  induction l as [ | x xs IHl].
  - inversion Ha.
  - simpl in *.
    destruct Ha.
    + left.
      subst ; reflexivity.
    + right.
      apply (IHl (fun a0 H => p a0 (or_intror H))).
Qed.
  
Global Instance isFinite_members
       {A : Type}
       (l : list A)
  : isFinite (members l).
Proof.
  simple refine {| els := els_members l l (fun _ H => H) ;
                   allIsMember := _ |}.
  abstract
    (intro x ;
     destruct x ;
     apply (in_els_members l l (fun _ H => H))).
Defined.

Definition dec_eq_members
           {A : Type}
           (l : list A)
           `{decEq A}
           (a1 a2 : members l)
  : dec (a1 = a2).
Proof.
  destruct a1 as [a1 p1], a2 as [a2 p2].
  destruct (dec_eq a1 a2) as [p | p].
  - refine (Yes _).
    abstract
      (subst ;
       f_equal ;
       apply proof_irrelevance).
  - refine (No _).
    abstract
      (intro q ;
       inversion q ;
       contradiction).
Defined.

Global Instance decEq_members
       {A : Type}
       (l : list A)
       `{decEq A}
  : decEq (members l)
  := {| dec_eq := dec_eq_members l |}.

(** * If we have a finite type and a decidable proposition on it, then we can decide whether that proposition holds for every element of that type. *)
Definition decide_finite_list
           {A : Type}
           (P : A -> Prop)
           (HP : forall (a : A), dec (P a))
           (l : list A)
  : dec (forall (a : A), In a l -> P a).
Proof.
  induction l as [ | x xs IHl ].
  - refine (Yes _).
    intros a q ; simpl in *.
    contradiction.
  - destruct (HP x) as [p | p].
    + destruct IHl as [q | q].
      * refine (Yes _) ; simpl.
        intros a Ha.
        destruct Ha.
        ** subst.
           assumption.
        ** apply q.
           exact H.
      * refine (No _).
        intros n.
        apply q.
        intros w Hw.
        apply n.
        right.
        assumption.
    + refine (No _) ; simpl.
      intro n.
      apply p.
      apply n.
      left.
      reflexivity.
Defined.

Definition decide_finite
           {A : Type}
           (P : A -> Prop)
           (HP : forall (a : A), dec (P a))
           `{isFinite A}
  : dec (forall (a : A), P a).
Proof.
  destruct (decide_finite_list P HP els) as [p | p].
  - refine (Yes _).
    intro a.
    apply p.
    apply allIsMember.
  - refine (No _).
    intro n.
    apply p.
    intros a ?.
    apply n.
Defined.

(** ** Decidable membership of lists *)
Definition decideIn
           {A : Type}
           `{decEq A}
           (a : A)
           (xs : list A)
  : dec (In a xs).
Proof.
  induction xs as [ | x xs IHxs ].
  - refine (No (fun q => _)).
    abstract
      (simpl in * ;
       contradiction).
  - destruct (dec_eq x a) as [ p | p ].
    + refine (Yes _).
      abstract
        (left ;
         exact p).
    + destruct IHxs as [ q | q ].
      * refine (Yes _).
        abstract
          (right ;
           exact q).
      * refine (No _).
        abstract
          (intro r ;
           induction r ;
           contradiction).
Defined.
