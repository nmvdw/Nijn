Require Import WellfoundedRelation.

(** * Transitive closures *)

(** The transitive closure *)
Inductive transitiveClosure {A : Type} (R : A -> A -> Type) : A -> A -> Type :=
| TStep : forall (a1 a2 : A),
    R a1 a2
    -> transitiveClosure R a1 a2
| Trans : forall {a1 a2 a3 : A},
    transitiveClosure R a1 a2
    -> transitiveClosure R a2 a3
    -> transitiveClosure R a1 a3.

Arguments TStep {_ _ _ _} _.
Arguments Trans {_ _ _ _ _} _ _.

(** * Wellfoundedness of the transitive closure *)

(** A relation is wellfounded if its transitive closure is wellfounded *)
Proposition wf_from_transitiveClosure
            {A : Type}
            (R : A -> A -> Type)
            (HR : Wf (transitiveClosure R))
  : Wf R.
Proof.
  refine (fiber_Wf HR (fun a => a) _).
  intros a1 a2 r.
  apply TStep.
  exact r.
Qed.

(** * Reflexive closure *)
Definition reflexiveClosure {A : Type} (R : A -> A -> Type) : A -> A -> Type :=
  fun a1 a2 => (R a1 a2 + (a1 = a2))%type.
