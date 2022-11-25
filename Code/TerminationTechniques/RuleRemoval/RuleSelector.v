Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import List.

(** * Rule selecting *)

(** When one uses rule removal, one needs to select the rules that will be removed. In this file, we define such predicates and we give several combinators for them.

Note that we use a predicate on the positions rather than a predicate on all possible rewrite rules. This way we don't need to compare rewrite rules when applying rule removal. *)
Section RuleSelector.
  Context {B F : Type}
          (X : afs B F).

  Record selector : Type :=
    {
      pred :> pos (list_of_rewriteRules X) -> Prop ;
      dec_pred : forall (i : pos (list_of_rewriteRules X)), dec (pred i)
    }.

  Definition select_all : selector :=
    {|
      pred i := True ;
      dec_pred i := dec_True
    |}.

  Definition select_none : selector :=
    {|
      pred i := False ;
      dec_pred i := dec_False
    |}.

  Definition select_not (P : selector) : selector :=
    {|
      pred i := ~(P i) ;
      dec_pred i := dec_not (dec_pred P i)
    |}.

  Definition select_and (P Q : selector) : selector :=
    {|
      pred i := P i /\ Q i ;
      dec_pred i := dec_and (dec_pred P i) (dec_pred Q i)
    |}.

  Definition select_or (P Q : selector) : selector :=
    {|
      pred i := P i \/ Q i ;
      dec_pred i := dec_or (dec_pred P i) (dec_pred Q i)
    |}.

  Definition select_pos (i : pos (list_of_rewriteRules X)) : selector :=
    {|
      pred j := i = j ;
      dec_pred j := dec_eq i j
    |}.

  Fixpoint select_list (i : list (pos (list_of_rewriteRules X))) : selector :=
    match i with
    | nil => select_none
    | i :: tl_i => select_or (select_pos i) (select_list tl_i)
    end.

  Definition select_list_nats
             (ns : list nat)
             (H : included (list_of_rewriteRules X) ns)
    : selector
    := select_list (list_nat_to_list_pos ns H).
End RuleSelector.

Arguments dec_pred {B F X} _ i.

(** If we have decidable equality on the base types and function symbols, then every rule selector gives rise to a decidable predicate on the rewrite rules. *)
Definition selector_members
           {B F : Type}
           `{decEq B}
           `{decEq F}
           {X : afs B F}
           (P : selector X)
           (r : rewriteRules X)
  : Prop
  := P (isMember_to_pos (in_to_isMember (member_isEl r))).

Definition dec_selector_members
           {B F : Type}
           `{decEq B}
           `{decEq F}
           {X : afs B F}
           (P : selector X)
           (r : rewriteRules X)
  : dec (selector_members P r).
Proof.
  apply (dec_pred P).
Defined.

Proposition all_selector_members
            {B F : Type}
            `{decEq B}
            `{decEq F}
            (X : afs B F)
            (Q : rewriteRules X -> Prop)
            (P : selector X)
            (HQ : forall (i : pos (list_of_rewriteRules X)), P i -> Q (listAtMembers i))
            (r : rewriteRules X)
            (Hr : selector_members P r)
  : Q r.
Proof.
  destruct r as [ r k ].
  pose (HQ (isMember_to_pos (in_to_isMember k)) Hr).
  refine (transport Q _ q).
  apply eq_MakeMem.
  apply isMember_listAt.
Qed.

(** ** Filter and removing rules from an AFS using a rule selector *)
Definition filter_rewrite_rules
           {B F : Type}
           (X : afs B F)
           (P : selector X)
  : list (rewriteRule (arity X))
  := filter_list (list_of_rewriteRules X) P (dec_pred P).

Definition filter_afs
           {B F : Type}
           (X : afs B F)
           (P : selector X)
  : afs B F
  := make_afs
       (arity X)
       (filter_rewrite_rules X P).

Definition remove_rewrite_rules
           {B F : Type}
           (X : afs B F)
           (P : selector X)
  : list (rewriteRule (arity X))
  := remove_list (list_of_rewriteRules X) P (dec_pred P).

Definition remove_afs
           {B F : Type}
           (X : afs B F)
           (P : selector X)
  : afs B F
  := make_afs
       (arity X)
       (remove_rewrite_rules X P).

Local Open Scope srp.

(** ** Rule selectors and strong reduction pairs *)

(** In the theorem for rule removal, two conditions need to be satisfied. These are expressed in the definition [respects_selector]. *)
Definition respects_selector
           {B F : Type}
           `{decEq B}
           `{decEq F}
           (X : afs B F)
           (A : strong_reduction_pair (arity X))
           (P : selector X)
  : Prop
  := (forall (r : rewriteRules X),
      selector_members P r
      -> lhs r ≺[ A ] rhs r)
     /\
     forall (r : rewriteRules X),
     ~(selector_members P r)
     -> lhs r ≼[ A ] rhs r.
