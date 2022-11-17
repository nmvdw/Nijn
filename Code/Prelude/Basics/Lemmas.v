Require Import Lia.
Require Import List.

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
  
(** Useful lemma in addition *)
Proposition plus_ge
            {n1 n2 m1 m2 : nat}
            (p : n1 >= n2)
            (q : m1 >= m2)
  : n1 + m1 >= n2 + m2.
Proof.
  lia.
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
