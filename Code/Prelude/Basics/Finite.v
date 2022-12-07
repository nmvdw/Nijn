Require Import Nijn.Prelude.Checks.
Require Import Nijn.Prelude.Funext.
Require Import Nijn.Prelude.Basics.Decidable.
Require Import List.

(** * Finite types *)

(** We define the notion of finite types, and for that, we use the enumerated types (also known as Kuratowski finite types). These are types for which we can write down a list that contains all the elements of that particular type. *)
Class isFinite (A : Type) :=
  {
    els : list A ;
    allIsMember : forall (a : A), In a els
  }.

(** * Examples of finite types *)

(** The unit type is finite *)
Global Instance isFinite_unit : isFinite unit.
Proof.
  simple refine {| els := tt :: nil ; allIsMember := _ |}.
  intro x.
  induction x.
  left.
  reflexivity.
Defined.

(** The booleans are finite *)
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

Definition eq_MakeMem
           {A : Type}
           {l : list A}
           {a1 a2 : A}
           (p : a1 = a2)
           {Ha1 : In a1 l}
           {Ha2 : In a2 l}
  : MakeMem a1 Ha1 = MakeMem a2 Ha2.
Proof.
  subst.
  f_equal.
  apply proof_irrelevance.
Qed.

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
    subst.
    f_equal.
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

(** * If we have a finite type and a decidable proposition on it, then we can decide whether that proposition holds for every element of that type and whether it holds for some element. *)
Lemma all_nil
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
      (a : A)
      (Ha : In a nil)
  : P a.
Proof.
  cbn in *.
  contradiction.
Qed.

Lemma all_no_head
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
      (x : A)
      (xs : list A)
      (Hx : ~(P x))
  : ~(forall (a : A), In a (x :: xs) -> P a).
Proof.
  intro H.
  apply Hx.
  apply H.
  cbn.
  left.
  reflexivity.
Qed.

Lemma all_no_tail
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
      (x : A)
      (xs : list A)
      (Hxs : ~(forall (a : A), In a xs -> P a))
  : ~(forall (a : A), In a (x :: xs) -> P a).
Proof.
  intros H.
  apply Hxs.
  intros a Ha.
  apply H.
  cbn.
  right.
  exact Ha.
Qed.

Lemma all_yes
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
      (x : A)
      (xs : list A)
      (Hx : P x)
      (Hxs : forall (a : A), In a xs -> P a)
  : forall (a : A), In a (x :: xs) -> P a.
Proof.
  intros a Ha.
  destruct Ha.
  - subst.
    exact Hx.
  - apply Hxs.
    exact H.
Qed.

Fixpoint decide_forall_finite_list
         {A : Type}
         (P : A -> Prop)
         (HP : forall (a : A), dec (P a))
         (l : list A)
  : dec (forall (a : A), In a l -> P a)
  := match l with
     | nil => Yes (all_nil P HP)
     | x :: xs =>
       match HP x with
       | No p => No (all_no_head P HP x xs p)
       | Yes p =>
         match decide_forall_finite_list P HP xs with
         | No q => No (all_no_tail P HP x xs q)
         | Yes q => Yes (all_yes P HP x xs p q)
         end
       end
     end.

Definition decide_forall_finite
           {A : Type}
           (P : A -> Prop)
           (HP : forall (a : A), dec (P a))
           `{isFinite A}
  : dec (forall (a : A), P a)
  := match decide_forall_finite_list P HP els with
     | Yes p => Yes (fun a => p _ (allIsMember _))
     | No p => No (fun n => p (fun a Ha => n a))
     end.

Lemma all_no_exists
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
  : ~(exists (a : A), In a nil /\ P a).
Proof.
  intro H.
  destruct H as [ a [ Ha1 Ha2 ]].
  cbn in *.
  contradiction.
Qed.

Lemma head_exists
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
      (x : A)
      (xs : list A)
      (Hx : P x)
  : exists (a : A), In a (x :: xs) /\ P a.
Proof.
  exists x.
  split ; cbn.
  - left.
    reflexivity.
  - exact Hx.
Qed.

Lemma tail_exists
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
      (x : A)
      (xs : list A)
      (Hxs : exists (a : A), In a xs /\ P a)
  : exists (a : A), In a (x :: xs) /\ P a.
Proof.
  destruct Hxs as [ a [ Ha1 Ha2 ]].
  exists a.
  split ; cbn.
  - right.
    exact Ha1.
  - exact Ha2.
Qed.

Lemma no_exists
      {A : Type}
      (P : A -> Prop)
      (HP : forall (a : A), dec (P a))
      (x : A)
      (xs : list A)
      (Hx : ~(P x))
      (Hxs : ~(exists (a : A), In a xs /\ P a))
  : ~(exists (a : A), In a (x :: xs) /\ P a).
Proof.
  intros n.
  destruct n as [ a [ Ha1 Ha2 ]] ; cbn in *.
  destruct Ha1 as [ p | p ].
  - apply Hx.
    subst.
    exact Ha2.
  - apply Hxs.
    exists a.
    split ; assumption.
Qed.

Fixpoint decide_exists_finite_list
         {A : Type}
         (P : A -> Prop)
         (HP : forall (a : A), dec (P a))
         (l : list A)
  : dec (exists (a : A), In a l /\ P a)
  := match l with
     | nil => No (all_no_exists P HP)
     | x :: xs =>
       match HP x with
       | Yes p => Yes (head_exists P HP x xs p)
       | No p =>
         match decide_exists_finite_list P HP xs with
         | No q => No (no_exists P HP x xs p q)
         | Yes q => Yes (tail_exists P HP x xs q)
         end
       end
     end.

Definition decide_exists_finite
           {A : Type}
           (P : A -> Prop)
           (HP : forall (a : A), dec (P a))
           `{isFinite A}
  : dec (exists (a : A), P a).
Proof.
  destruct (decide_exists_finite_list P HP els) as [ p | p ].
  - apply Yes.
    destruct p as [ a Ha ].
    exists a.
    apply Ha.
  - apply No.
    intro n.
    apply p.
    destruct n as [ a Ha ].
    exists a.
    split.
    + apply allIsMember.
    + exact Ha.
Defined.

(** * Decidable membership of lists *)
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

(** * Proof-relevant membership *)

(** We define a proof relevant membership relation for lists. *)
Inductive isMember {A : Type} : A -> list A -> Type :=
| Here : forall (a₁ a₂ : A) (xs : list A) (p : a₁ = a₂), isMember a₁ (a₂ :: xs)
| There : forall {a : A} (x : A) {xs : list A},
    isMember a xs -> isMember a (x :: xs).

Notation "a ∈ l" := (isMember a l) (at level 60).

(** We can relate [a ∈ l] to [In a l]. The former always implies the latter. *)
Definition isMember_to_in
           {A : Type}
           {a : A}
           {l : list A}
           (p : a ∈ l)
  : In a l.
Proof.
  induction p.
  - subst.
    apply in_eq.
  - apply in_cons.
    apply IHp.
Qed.

(** For the converse, we need to assume decidable equality. We also use the following lemma. *)
Lemma in_tail
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

Program Fixpoint in_to_isMember
         {A : Type}
         `{decEq A}
         {a : A}
         {l : list A}
  : In a l -> a ∈ l
  := match l with
     | nil => fun p => False_rect _ _
     | x :: xs =>
       fun p =>
         match dec_eq a x with
         | Yes e => Here _ _ _ _
         | No e => There _ (in_to_isMember (in_tail p e))
         end
     end.

(** Properties of [isMember] *)
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
    assumption.
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
    f_equal.
    assumption.
  - apply There.
    exact IHp.
Defined.
