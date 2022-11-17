Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Coq.Program.Equality.
Require Import Lia.
Require Import List.

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
End RuleSelector.

Arguments dec_pred {B F X} _ i.

Definition selector_members
           {B F : Type}
           `{decEq B}
           `{decEq F}
           (X : afs B F)
           (P : selector X)
           (r : rewriteRules X)
  : Prop
  := P (isMember_to_pos (in_to_isMember (member_isEl r))).

Definition dec_selector_members
           {B F : Type}
           `{decEq B}
           `{decEq F}
           (X : afs B F)
           (P : selector X)
           (r : rewriteRules X)
  : dec (selector_members X P r).
Proof.
  apply (dec_pred P).
Defined.
             
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

Definition respects_selector
           {B F : Type}
           `{decEq B}
           `{decEq F}
           (X : afs B F)
           (A : strong_reduction_pair (arity X))
           (P : selector X)
  : Prop
  := (forall (r : rewriteRules X),
      selector_members X P r
      -> lhs r ≺[ A ] rhs r)
     /\
     forall (r : rewriteRules X),
     ~(selector_members X P r)
     -> lhs r ≼[ A ] rhs r.
