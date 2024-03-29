Require Import Nijn.Prelude.Basics.Decidable.
Require Import Nijn.Prelude.Basics.Finite.
Require Import Lia.
Require Import List.
Require Import Coq.Program.Equality.

(** * Positions in lists *)

(** For every list there is a type of positions. Each of these positions points to a concrete place in that list. *)
Inductive pos {A : Type} : list A -> Type :=
| Hd : forall (x : A) (xs : list A), pos (x :: xs)
| Tl : forall {x : A} {xs : list A}, pos xs -> pos (x :: xs).

(** Given a position, we can pick the element at that place. *)
Fixpoint listAt {A : Type} {l : list A} (i : pos l) : A :=
  match i with
  | Hd x xs => x
  | Tl i => listAt i
  end.

Proposition in_listAt {A : Type} {l : list A} (i : pos l)
  : In (listAt i) l.
Proof.
  induction i as [ x xs | x xs i Hi ] ; cbn.
  - left.
    reflexivity.
  - right.
    exact Hi.
Defined.

Definition listAtMembers {A : Type} {l : list A} (i : pos l) : members l
  := MakeMem (listAt i) (in_listAt i).

(** We can map the natural numbers to positions *)
Program Fixpoint nat_to_pos
                 {A : Type}
                 {l : list A}
  : forall (n : nat)
           (H : n < length l),
    pos l
  := match l with
     | nil => fun n H => False_rect _ _
     | cons x xs =>
       fun n =>
       match n with
       | 0 => fun H => Hd _ _
       | S n => fun H => Tl (nat_to_pos n _)
       end
     end.
Next Obligation.
  lia.
Qed.
Next Obligation.
  lia.
Qed.

Fixpoint included
         {A : Type}
         (l : list A)
         (ns : list nat)
  : Prop
  := match ns with
     | nil => True
     | n :: ns => n < length l /\ included l ns
     end.

Program Fixpoint list_nat_to_list_pos
                 {A : Type}
                 {l : list A}
                 (ns : list nat)
  : forall (H : included l ns),
    list (pos l)
  := match ns with
     | nil => fun _ => nil
     | n :: ns => fun H => nat_to_pos n _ :: list_nat_to_list_pos ns _
     end.

(** From a member of the list, we obtain a position *)
Definition isMember_to_pos
           {A : Type}
           {a : A} {l : list A}
           (H : a ∈ l)
  : pos l.
Proof.
  induction H.
  - apply Hd.
  - apply Tl.
    assumption.
Defined.

(** ** Filtering and removing elements from the list *)

(** If we have a decidable predicate on the positions, then we can remove the positions for which that predicate holds and we can remove the positions for which that predicate does not hold. *)
Definition pos_tl
           {A : Type}
           {x : A}
           {xs : list A}
           (P : pos (x :: xs) -> Prop)
  : pos xs -> Prop
  := fun i => P (Tl i).

Definition dec_pos_tl
           {A : Type}
           {x : A}
           {xs : list A}
           (P : pos (x :: xs) -> Prop)
           (decP : forall (i : pos (x :: xs)), dec (P i))
           (i : pos xs)
  : dec (pos_tl P i)
  := match decP (Tl i) with
     | Yes p => Yes p
     | No q => No q
     end.

Fixpoint filter_list
         {A : Type}
         (l : list A)
  : forall (P : pos l -> Prop)
           (decP : forall (i : pos l), dec (P i)),
    list A
  := match l with
     | nil => fun P decP => nil
     | cons x xs =>
       fun P decP =>
       let rest := filter_list xs (pos_tl P) (dec_pos_tl P decP) in
       match decP (Hd x xs) with
       | Yes _ => cons x rest
       | No _ => rest
       end
     end.

Fixpoint remove_list
         {A : Type}
         (l : list A)
  : forall (P : pos l -> Prop)
           (decP : forall (i : pos l), dec (P i)),
    list A
  := match l with
     | nil => fun P decP => nil
     | cons x xs =>
       fun P decP =>
       let rest := remove_list xs (pos_tl P) (dec_pos_tl P decP) in
       match decP (Hd x xs) with
       | No _ => cons x rest
       | Yes _ => rest
       end
     end.

(** Membership after removing *)
Proposition In_remove_list
            {A : Type}
            {l : list A}
            (P : pos l -> Prop)
            (decP : forall (i : pos l), dec (P i))
            (i : pos l)
            (Hi : ~(P i))
  : In (listAt i) (remove_list l P decP).
Proof.
  induction i as [ x xs | x xs i IHi ] ; cbn ; destruct (decP (Hd x xs)) ; cbn.
  - contradiction.
  - left.
    reflexivity.
  - apply IHi.
    exact Hi.
  - right.
    apply IHi.
    exact Hi.
Qed.

Proposition isMember_listAt
            {A : Type}
            {l : list A}
            (a : A)
            (H : a ∈ l)
  : listAt (isMember_to_pos H) = a.
Proof.
  induction H.
  - subst.
    reflexivity.
  - assumption.
Qed.

Proposition members_listAt
            {A : Type}
            `{decEq A}
            {l : list A}
            (r : members l)
  : listAt (isMember_to_pos (in_to_isMember (member_isEl r))) = member_el r.
Proof.
  apply isMember_listAt.
Qed.

Proposition In_remove_list_member
            {A : Type}
            `{decEq A}
            {l : list A}
            (P : pos l -> Prop)
            (decP : forall (i : pos l), dec (P i))
            (r : members l)
            (Hr : ~(P (isMember_to_pos (in_to_isMember (member_isEl r)))))
  : In (member_el r) (remove_list l P decP).
Proof.
  assert (listAt (isMember_to_pos (in_to_isMember (member_isEl r))) = member_el r) as p.
  {
    apply members_listAt.
  }
  rewrite <- p.
  apply In_remove_list.
  exact Hr.
Qed.

(** ** Decidable equality of positions *)
Fixpoint pos_to_nat
         {A : Type}
         {l : list A}
         (i : pos l)
  : nat
  := match i with
     | Hd _ _ => 0
     | Tl j => S(pos_to_nat j)
     end.

Proposition pos_to_nat_lt
            {A : Type}
            {l : list A}
            (i : pos l)
  : pos_to_nat i < length l.
Proof.
  induction i as [ x xs | x xs i Hi ] ; cbn.
  - lia.
  - lia.
Qed.

Proposition pos_to_nat_to_pos
            {A : Type}
            {l : list A}
            (i : pos l)
            (H : pos_to_nat i < length l)
  : nat_to_pos (pos_to_nat i) H = i.
Proof.
  induction i as [ x xs | x xs i Hi ] ; cbn.
  - reflexivity.
  - f_equal.
    apply Hi.
Qed.
  
Proposition pos_tonat_eq
            {A : Type}
            {l : list A}
            {i j : pos l}
            (p : pos_to_nat i = pos_to_nat j)
  : i = j.
Proof.
  induction i.
  - dependent destruction j.
    + reflexivity.
    + cbn in p.
      discriminate.
  - dependent destruction j.
    + simpl in p.
      discriminate.
    + f_equal.
      apply IHi.
      simpl in p.
      inversion p.
      reflexivity.
Qed.

Definition dec_eq_pos
           {A : Type}
           {l : list A}
           (i j : pos l)
  : dec (i = j)
  := match dec_eq (pos_to_nat i) (pos_to_nat j) with
     | Yes p => Yes (pos_tonat_eq p)
     | No p => No (fun q => p (f_equal _ q))
     end.
  
Global Instance decEq_pos {A : Type} (l : list A) : decEq (pos l) :=
  {| dec_eq := dec_eq_pos |}.

Proposition all_pos
            {A : Type}
            {l : list A}
            (P : pos l -> Prop)
            (H : forall (n : nat) (H : n < length l), P (nat_to_pos n H))
            (i : pos l)
  : P i.
Proof.
  simple refine (transport P _ (H (pos_to_nat i) (pos_to_nat_lt i))).
  rewrite pos_to_nat_to_pos.
  reflexivity.
Qed.
