Require Import Prelude.Funext.
Require Import Prelude.Basics.
Require Import Preprocessing.TypeChecker.
Require Import Preprocessing.PreprocessTerm.
Require Import Signature.
Require Import List.
Require Import Coq.Program.Equality.
Require Import Prelude.Funext.

(* For rewriting rules, use *)

(** Help functions *)
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

Fixpoint list_option
         {A : Type}
         (l : list (option A))
  : option (list A)
  := match l with
     | nil => Some nil
     | x :: xs =>
       match list_option xs with
       | Some ys =>
         match x with
         | Some y => Some (y :: ys)
         | None => None
         end
       | None => None
       end
     end.

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

Definition assocList
           (A B : Type)
  : Type
  := list (A * B).

Program Fixpoint getKey
        {A B : Type}
        `{decEq A}
        (a : A)
        (xs : assocList A B)
  : option { b : B | In (pair a b) xs }
  := match xs with
     | nil => None
     | (pair x b) :: xs =>
       match dec_eq x a with
       | Yes p => Some (exist _ b _)
       | No p =>
         match getKey a xs with
         | Some (exist _ b' p) => Some (exist _ b' _)
         | None => None
         end
       end
     end.

Definition not_hd_cons
           {A : Type}
           {a x : A}
           {xs : list A}
           (p : x <> a)
           (q : In a (x :: xs))
  : In a xs.
Proof.
  simpl in q.
  destruct q ; try contradiction.
  assumption.
Qed.

Definition fst_list
           {A : Type}
           {B : A -> Type}
           (l : list { a : A & B a})
  : list A
  := map (@projT1 A B) l.

Fixpoint dmap
         {A : Type}
         {B : A -> Type}
         (f : forall (a : A), B a)
         (l : list A)
  : list { a : A & B a }
  := match l with
     | nil => nil
     | x :: xs => (x , f x) :: dmap f xs
     end.

Fixpoint list_option_pair
         {A : Type}
         {B : A -> Type}
         (l : list { a : A & option (B a) })
  : option (list { a : A & B a })
  := match l with
     | nil => Some nil
     | (x , Some p) :: xs =>
       match list_option_pair xs with
       | Some xs => Some ((x , p) :: xs)
       | None => None
       end
     | (x , None) :: xs => None
     end.

Fixpoint list_to_map_el
         {A : Type}
         {B : A -> Type}
         `{decEq A}
         `{isFinite A}
         (l : list { a : A & B a })
  : forall (a : A), In a (fst_list l) -> B a
  := match l with
     | nil => fun a p => False_rect _ p
     | (x , z) :: xs =>
       fun a p =>
         match dec_eq x a with
         | Yes q => transport B q z
         | No q => list_to_map_el xs a (not_hd_cons q p)
         end
     end.

Definition list_to_map
           {A : Type}
           {B : A -> Type}
           `{decEq A}
           `{isFinite A}
           (l : list { a : A & B a })
           (p : forall (a : A), In a (fst_list l))
  : forall (a : A), B a.
Proof.
  intro a.
  specialize (p a).
  exact (list_to_map_el _ _ p).
Defined.

Proposition in_dmap
            {A : Type}
            {B : A -> Type}
            (f : forall (a : A), B a)
            (xs : list A)
            (a : A)
            (p : In a xs)
  : In a (fst_list (dmap f xs)).
Proof.
  induction xs as [ | x xs IHxs ] ; simpl in *.
  - contradiction.
  - destruct p as [ p | p ].
    + left.
      exact p.
    + right.
      apply IHxs.
      exact p.
Qed.

Definition in_list_option_pair
           {A : Type}
           {B : A -> Type}
           {l1 : list { a : A & option (B a) }}
           {l2 : list { a : A & B a }}
           (p : list_option_pair l1 = Some l2)
           (a : A)
           (q : In a (fst_list l1))
  : In a (fst_list l2).
Proof.
  revert l2 p.
  induction l1 as [ | x xs IHxs ] ; intros l2 p.
  - simpl in *.
    contradiction.
  - simpl in *.
    destruct x as [ x [ z | ]].
    destruct (list_option_pair xs) as [ ys | ] ; simpl in *.
    + inversion p.
      subst ; simpl.
      destruct q as [ q | q ].
      * left.
        exact q.
      * right.
        apply IHxs.
        ** exact q.
        ** reflexivity.
    + discriminate.
    + discriminate.
Qed.

Definition finite_option
           {A : Type}
           {B : A -> Type}
           `{isFinite A}
           `{decEq A}
           (f : forall (a : A), option (B a))
  : option (forall (a : A), B a).
Proof.
  pose (l := list_option_pair (dmap f els)).
  assert (Hl : list_option_pair (dmap f els) = l) by reflexivity.
  revert Hl.
  destruct l as [ l | ] ; intros p.
  - refine (Some _).
    simple refine (list_to_map l _).
    intro a.
    apply (in_list_option_pair p).
    apply in_dmap.
    apply allIsMember.
  - exact None.
Defined.

(** * The output of the parser *)
Record parsedAFS (B V F : Type) : Type :=
  {
    TypeSymbols : list B ;
    BaseTerms : assocList F (ty B) ;
    FreeVars : assocList V (ty B) ;
    Rewrites : list (rawNe V F * rawNf V F)
  }.

Arguments TypeSymbols {_ _ _} _.
Arguments BaseTerms {_ _ _} _.
Arguments FreeVars {_ _ _} _.
Arguments Rewrites {_ _ _} _.

(** Accessors for AFS *)
Definition baseTypes
           {B V F : Type}
           (X : parsedAFS B V F)
  : Type
  := members (TypeSymbols X).

Fixpoint to_baseType
         {B V F : Type}
         `{decEq B}
         (X : parsedAFS B V F)
         (A : ty B)
  : option (ty (baseTypes X))
  := match A with
     | Base b =>
       match decideIn b (TypeSymbols X) with
       | Yes p => Some (Base (MakeMem b p))
       | No p => None
       end
     | A1 ⟶ A2 =>
       match to_baseType X A1 , to_baseType X A2 with
       | Some A1 , Some A2 => Some (A1 ⟶ A2)
       | _ , _ => None
       end
     end.

(** * Processing to an AFS *)
Definition afs_arity
           {B V F : Type}
           `{decEq B}
           `{decEq F}
           (X : parsedAFS B V F)
  : option (members (BaseTerms X) -> ty (baseTypes X))
  := finite_option (fun p => to_baseType X (snd (member_el p))).

Fixpoint list_to_con
         {B : Type}
         (l : list (ty B))
  : con B
  := match l with
     | nil => ∙
     | x :: xs => x ,, list_to_con xs
     end.

Definition freeVars_to_con
           {B V F : Type}
           `{decEq B}
           (X : parsedAFS B V F)
  : option (con (baseTypes X))
  := let l := map (fun z => to_baseType X (snd z)) (FreeVars X) in
     match list_option l with
     | Some tys => Some (list_to_con tys)
     | None => None
     end.

Fixpoint check_functions_Nf
         {B V F : Type}
         `{decEq B}
         `{decEq F}
         `{decEq V}
         (X : parsedAFS B V F)
         (C : con (baseTypes X))
         (ar : members (BaseTerms X) -> ty (baseTypes X))
         (t : rawNf V F)
  : option (rawNf V (members (BaseTerms X)))
  := match t with
     | RawNeToNf t =>
       match check_functions_Ne X C ar t with
       | Some t => Some (RawNeToNf t)
       | None => None
       end
     | RawNfLam x t =>
       match check_functions_Nf X C ar t with
       | Some t => Some (RawNfLam x t)
       | None => None
       end
     end
with check_functions_Ne
     {B V F : Type}
     `{decEq B}
     `{decEq F}
     `{decEq V}
     (X : parsedAFS B V F)
     (C : con (baseTypes X))
     (ar : members (BaseTerms X) -> ty (baseTypes X))
     (t : rawNe V F)
  : option (rawNe V (members (BaseTerms X)))
  := match t with
     | RawNeVar v => Some (RawNeVar v)
     | RawNeBase f =>
       match getKey f (BaseTerms X) with
       | Some p => Some (RawNeBase (MakeMem (pair f (proj1_sig p)) (proj2_sig p)))
       | None => None
       end
     | RawNeApp f t =>
       match check_functions_Ne X C ar f , check_functions_Nf X C ar t with
       | Some f , Some t => Some (RawNeApp f t)
       | _ , _ => None
       end
     end.

Definition to_rewriteRule
           {B V F : Type}
           `{decEq F}
           `{decEq B}
           `{decEq V}
           {X : parsedAFS B V F}
           (ar : members (BaseTerms X) -> ty (baseTypes X))
           (t : rawNe V F * rawNf V F)
  : option (rewriteRule ar)
  := match t with
     | pair t1 t2 =>
       match freeVars_to_con X with
       | Some C =>
         match check_functions_Ne X C ar t1 with
         | Some t1 =>
           match rawNfToUtNe t1 with
           | Some t1 =>
             match infer_to_tm C ar t1 with
             | Some (A , t1) =>
               match check_functions_Nf X C ar t2 with
               | Some t2 =>
                 match rawNfToUtNf t2 with
                 | Some t2 =>
                   match check_to_tm C ar t2 A with
                   | Some t2 => Some (make_rewrite C _ t1 t2)
                   | None => None
                   end
                 | None => None
                 end
               | None => None
               end
             | None => None
             end
           | None => None
           end
         | None => None
         end
       | None => None
       end
     end.

Definition parsedAFS_to_afs
           {B V F : Type}
           `{decEq B}
           `{decEq F}
           `{decEq V}
           (X : parsedAFS B V F)
  : option (afs (baseTypes X) (members (BaseTerms X)))
  := match afs_arity X with
     | Some ar =>
       match freeVars_to_con X with
       | Some C =>
         match list_option (map (to_rewriteRule ar) (Rewrites X)) with
         | Some rs => Some (make_afs ar rs)
         | None => None
         end
       | None => None
       end
     | None => None
     end.

Require Import Extraction.
Recursive Extraction parsedAFS_to_afs.
