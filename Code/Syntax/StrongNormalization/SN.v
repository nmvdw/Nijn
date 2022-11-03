Require Import Prelude.WellfoundedRelation.
Require Import Syntax.Signature.
Require Import Syntax.Signature.RewriteLemmas.

Import AFSNotation.

(** * Strong normalization *)

(** An AFS is strongly normalizing if the rewriting relation is well-founded *)
Definition isSN
           {B F : Type}
           (X : afs B F)
  : Prop
  := forall (C : con B) (A : ty B), Wf (fun (t1 t2 : tm X C A) => t1 ~> t2).

(** A type is said to be strongly normalizing if the rewrite relations of terms on that type is strongly normalizing *)
Definition Ty_isSN
           {B F : Type}
           (X : afs B F)
           (A : ty B)
  : Prop
  := forall (C : con B), Wf (fun (t1 t2 : tm X C A) => t1 ~> t2).

(** We show that if one type is strongly normalizing, then all types are. Hence, it is sufficient to check for strong normalization in just one type. *)
Definition map_Tm
           {B F : Type}
           {X : afs B F}
           {C : con B}
           (A : ty B)
           {A' : ty B}
           (t : tm X C A')
  : tm X ((A' ⟶ A),, C) A
  := TmVar Vz · wkTm t (Drop _ (idWk C)).

Definition Rew_map_Tm
           {B F : Type}
           {X : afs B F}
           {C : con B}
           {A A' : ty B}
           {t1 t2 : tm X C A'}
           (p : t1 ~> t2)
  : map_Tm A t1 ~> map_Tm A t2.
Proof.
  unfold map_Tm.
  apply rew_App_r.
  apply Rew_Wk.
  exact p.
Qed.

Theorem SN_if_TySN
        {B F : Type}
        (X : afs B F)
        (A : ty B)
        (H : Ty_isSN X A)
  : isSN X.
Proof.
  intros C A'.
  simple refine (fiber_Wf (H ((A' ⟶ A) ,, C)) _ _).
  - exact (map_Tm _).
  - intros t1 t2.
    exact Rew_map_Tm.
Qed.    
