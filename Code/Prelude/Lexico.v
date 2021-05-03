Require Import WellfoundedRelation.
Require Import CompatibleRelation.

(** * The lexicographic order *)

Section Lexico.
  Context (X : CompatRel)
          {Y : Type}
          `{isCompatRel X}
          (RY : Y -> Y -> Type).

  (** Given a compatible relation and a type with a relation on it, then we can define the lexicographic order on the product. *)
  Definition lexico
    : X * Y -> X * Y -> Type
    := fun x y => ((gt (fst x) (fst y))
                   +
                   ((fst x >= fst y) * RY (snd x) (snd y)))%type.

  (** Transitivity for the lexicographic order *)
  Proposition lexico_trans
              (RYtrans : forall (y1 y2 y3 : Y),
                  RY y1 y2 -> RY y2 y3 -> RY y1 y3)
              {x y z : X * Y}
              (p : lexico x y)
              (q : lexico y z)
    : lexico x z.
  Proof.
    destruct p as [p | [p1 p2]], q as [q | [q1 q2]].
    - left.
      exact (gt_trans p q).
    - left.
      exact (gt_ge p q1).
    - left.
      exact (ge_gt p1 q).
    - right.
      split.
      + exact (ge_trans p1 q1).
      + exact (RYtrans _ _ _ p2 q2).
  Qed.

  (** Wellfoundedness of the lexicographic order *)
  Proposition lexico_Wf_help
              (x : X * Y)
              (z1 : X)
              (p : fst x >= z1)
              (HX : isWf lexico x)
    : isWf lexico (z1 , snd x).
  Proof.
    revert p.
    revert z1.
    induction HX as [[q1 q2] Hq IHq].
    simpl in *.
    intros z1 p.
    apply acc.
    intros [w1 w2] [H' | [H1 H2]] ; simpl in *.
    - refine (IHq (w1 , w2) _ w1 _) ; simpl.
      + left ; simpl.
        exact (ge_gt p H').
      + apply ge_refl.
    - refine (IHq (q1 , w2) _ w1 _).
      + right ; simpl.
        split.
        * apply ge_refl.
        * exact H2.
      + refine (ge_trans p H1).
  Qed.

  Proposition lexico_Wf
              (HX : Wf (fun (x y : X) => x > y))
              (HY : Wf RY)
    : Wf lexico.
  Proof.
    intros [x y].
    pose (HX x) as Hx.
    revert y.
    induction Hx as [x Hx IHx].
    intros y.
    pose (HY y) as Hy.
    induction Hy as [y Hy IHy].
    apply acc.
    intros [z1 z2] [Hz | [Hz1 Hz2]] ; simpl in *.
    - apply IHx.
      exact Hz.
    - refine (lexico_Wf_help (x , _) z1 Hz1 _).
      exact (IHy z2 Hz2).
  Qed.
End Lexico.
