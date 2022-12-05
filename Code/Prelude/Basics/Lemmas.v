Require Import Lia.
Require Import List.

(** * Basic lemmas and functions *)

(** ** Empty lists and membership*)
Definition isNil {A : Type} (l : list A) : Prop :=
  match l with
  | nil => True
  | _ => False
  end.

Proposition isNil_no_member
            {A : Type}
            (l : list A)
            (Hl : isNil l)
            (x : A)
  : ~(In x l).
Proof.
  induction l ; cbn in *.
  - exact (fun z => z).
  - contradiction.
Qed.
  
(** ** Lemma about addition *)
Proposition plus_ge
            {n1 n2 m1 m2 : nat}
            (p : n1 >= n2)
            (q : m1 >= m2)
  : n1 + m1 >= n2 + m2.
Proof.
  lia.
Qed.

Proposition mult_ge
            {k n m : nat}
            (p : n >= m)
  : k * n >= k * m.
Proof.
  nia.
Qed.

(** ** Basics functions *)

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
