Require Import Prelude.Basics.
Require Import Signature.
Require Import String.
Require Import List.
Require Import Coq.Program.Equality.

Local Open Scope string.

(** * Pretty printing of terms *)

(** ** Terms with named variables *)
Inductive rawTm (V : Type) (F : Type) : Type :=
| RawVar : V -> rawTm V F
| RawBase : F -> rawTm V F
| RawLam : V -> rawTm V F -> rawTm V F
| RawApp : rawTm V F -> rawTm V F -> rawTm V F.

Arguments RawVar {_ _} _.
Arguments RawBase {_ _} _.
Arguments RawLam {_ _} _ _.
Arguments RawApp {_ _} _ _.

(** ** Conversion of well-typed terms to named terms *)

(**
To do so, we need to assign to every variable a name.
For that reason, we assign to every index in the context a name.
 *)
Inductive conNames {B : Type} (V : Type) : con B -> Type :=
| EmptyNames : conNames V ∙
| ExtendName : forall {A : ty B} {C : con B},
    V -> conNames V C -> conNames V (A ,, C).

Arguments EmptyNames {_ _}.
Arguments ExtendName {_ _ _ _} _ _.

Definition getName
           {B V : Type}
           {C : con B}
           {A : ty B}
           (names : conNames V C)
           (v : var C A)
  : V.
Proof.
  induction v.
  - inversion names.
    assumption.
  - inversion names.
    apply IHv.
    assumption.
Defined.

(** We also need the length of contexts*)
Fixpoint length {B : Type} (C : con B) : nat
  := match C with
     | ∙ => 0
     | _ ,, C => S(length C)
     end.

(**
To work with fresh variables, we assume that we can map natural numbers to variables.
To each context, we can assign names by picking fresh variables.
 *)
Definition nameCon
         {B : Type}
         {V : Type}
         (fresh : nat -> V)
         (C : con B)
         {n : nat}
         (p : length C = n)
  : conNames V C.
Proof.
  revert n p.
  induction C ; intros n p.
  - exact EmptyNames.
  - simpl in p.
    destruct n.
    + discriminate.
    + simple refine (ExtendName (fresh n) (IHC n _)).
      inversion p.
      reflexivity.
Defined.

(** ** Converting terms to well-typed terms *)
Fixpoint tmToRawTm_help
         {B F V : Type}
         {ar : F -> ty B}
         {C : con B}
         {A : ty B}
         (fresh : nat -> V)
         (names : conNames V C)
         {n : nat}
         (p : n = length C)
         (t : tm ar C A)
  : rawTm V F
  := match t with
     | TmVar v => RawVar (getName names v)
     | BaseTm f => RawBase f
     | Lam f =>
       let v := fresh n in
       RawLam v (tmToRawTm_help fresh (ExtendName v names) (f_equal S p) f)
     | App f t => RawApp (tmToRawTm_help fresh names p f) (tmToRawTm_help fresh names p t) 
     end.

Definition tmToRawTm
           {B F V : Type}
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (fresh : nat -> V)
           (t : tm ar C A)
  : rawTm V F
  := tmToRawTm_help fresh (nameCon fresh _ eq_refl) eq_refl t.

(** * Printing afs *)

(** To print an afs, we need the following data *)
Record afs_show (S : Type) (B : Type) (V : Type) (F : Type) : Type :=
  make_afs_show
    {
      (** Basic stuff *)
      startTypes : S ;
      startTerms : S ;
      startRewrites : S ;
      append : S -> S -> S ;
      leftParen : S ;
      rightParen : S ;
      separate : S ;
      empty : S ;
      colon : S ;
      fresh : nat -> V ;

      (** Printing types *)
      showBase : B -> S ;
      arrow : S ;

      (** Printing terms *)
      showBaseFun : F -> S ;
      showVars : V -> S ;
      showLam : S ;
      showLamSep : S ;
      appSep : S ;

      (** Rewrite rule *)
      rewriteSym : S
    }.

Arguments startTypes {_ _ _ _} _.
Arguments startTerms {_ _ _ _} _.
Arguments startRewrites {_ _ _ _} _.

Arguments append {_ _ _ _} _ _ _.
Arguments leftParen {_ _ _ _} _.
Arguments rightParen {_ _ _ _} _.
Arguments empty {_ _ _ _} _.
Arguments separate {_ _ _ _} _.
Arguments colon {_ _ _ _} _.
Arguments fresh {_ _ _ _} _ _.

Arguments showBase {_ _ _ _} _ _.
Arguments arrow {_ _ _ _} _.

Arguments showBaseFun {_ _ _ _} _ _.
Arguments showVars {_ _ _ _} _ _.
Arguments showLam {_ _ _ _} _.
Arguments showLamSep {_ _ _ _} _.
Arguments appSep {_ _ _ _} _.

Arguments rewriteSym {_ _ _ _} _.

(** Showing list *)
Fixpoint showList
         {S B V F : Type}
         (p : afs_show S B V F)
         (l : list S)
  : S
  := match l with
     | nil => empty p
     | cons x xs => append p x (append p (separate p) (showList p xs))
     end.

(** Showing parentheses *)
Definition showParen
           {S B V F : Type}
           (p : afs_show S B V F)
           (s : S)
  : S
  := append p (append p (leftParen p) s) (rightParen p).

(** Show function types *)
Definition showFunctionType
           {S B V F : Type}
           (p : afs_show S B V F)
           (s1 s2 : S)
  : S
  := append p s1 (append p (arrow p) s2).

(** Showing types *)
Fixpoint showType
         {S B V F : Type}
         (p : afs_show S B V F)
         (A : ty B)
  : S
  := match A with
     | Base b => showBase p b
     | A1 ⟶ A2 => showFunctionType p (showOther p A1) (showType p A2)
     end
with showOther
     {S B V F : Type}
     (p : afs_show S B V F)
     (A : ty B)
  : S
  := match A with
     | Base b => showBase p b
     | A1 ⟶ A2 => showParen p (showFunctionType p (showOther p A1) (showType p A2))
     end.

(** Showing terms *)
Definition showApplication
           {S B V F : Type}
           (p : afs_show S B V F)
           (s1 s2 : S)
  : S
  := append p s1 (append p (appSep p) s2).

Definition showLambdaTm
           {S B V F : Type}
           (p : afs_show S B V F)
           (v : V)
           (s : S)
  : S
  := append
       p
       (showLam p)
       (append
          p
          (showVars p v)
          (append
             p
             (showLamSep p)
             s)).

Fixpoint showRawTm
         {S B V F : Type}
         (p : afs_show S B V F)
         (t : rawTm V F)
  : S
  := match t with
     | RawVar v => showVars p v
     | RawBase f => showBaseFun p f
     | RawApp t1 t2 => showApplication
                         p
                         (showRawTmApp p t1)
                         (showRawTmVar p t2)
     | RawLam v t => showLambdaTm p v (showRawTm p t)
     end
with showRawTmApp
     {S B V F : Type}
     (p : afs_show S B V F)
     (t : rawTm V F)
  : S
  := match t with
     | RawVar v => showVars p v
     | RawBase f => showBaseFun p f
     | RawApp t1 t2 => showApplication
                         p
                         (showRawTmApp p t1)
                         (showRawTmVar p t2)
     | RawLam v t => showParen p (showLambdaTm p v (showRawTm p t))
     end
with showRawTmVar
     {S B V F : Type}
     (p : afs_show S B V F)
     (t : rawTm V F)
  : S
  := match t with
     | RawVar v => showVars p v
     | RawBase f => showBaseFun p f
     | RawApp t1 t2 => showParen
                         p
                         (showApplication
                            p
                            (showRawTmApp p t1)
                            (showRawTmVar p t2))
     | RawLam v t => showParen p (showLambdaTm p v (showRawTm p t))
     end.

Definition showTm
           {S B V F : Type}
           (p : afs_show S B V F)
           {ar : F -> ty B}
           {C : con B}
           {A : ty B}
           (fresh : nat -> V)
           (t : tm ar C A)
  : S
  := showRawTm p (tmToRawTm fresh t).
  
(** Showing an afs *)
Definition show_afs_types
           {S B V F : Type}
           (p : afs_show S B V F)
           (X : fin_afs B F)
  : S
  := append
       p
       (startTypes p)
       (append
          p
          (separate p)
          (showList p (map (showBase p) (@els _ (baseTyFin X))))).

Definition show_function_symbol
           {S B V F : Type}
           (p : afs_show S B V F)
           (X : fin_afs B F)
           (f : F)
  : S
  := append
       p
       (showBaseFun p f)
       (append
          p
          (colon p)
          (showType p (arity X f))).

Definition show_afs_functions
           {S B V F : Type}
           (p : afs_show S B V F)
           (X : fin_afs B F)
  : S
  := append
       p
       (startTerms p)
       (append
          p
          (separate p)
          (showList
             p
             (map (show_function_symbol p X)
                  (@els _ (baseTmFin X))))).

Definition show_rewrite
           {S B V F : Type}
           (p : afs_show S B V F)
           (X : fin_afs B F)
           (r : rewriteRule (arity X))
  : S
  := append
       p
       (showTm p (fresh p) (lhs_of r))
       (append
          p
          (rewriteSym p)
          (showTm p (fresh p) (rhs_of r))).

Definition show_afs_rewrites
           {S B V F : Type}
           (p : afs_show S B V F)
           (X : fin_afs B F)
  : S
  := append
       p
       (startRewrites p)
       (append
          p
          (separate p)
          (showList p (map (show_rewrite p X) (list_of_rewriteRules X)))).

Definition show_afs
           {S B V F : Type}
           (p : afs_show S B V F)
           (X : fin_afs B F)
  : S
  := append
       p
       (show_afs_types p X)
       (append
          p
          (append p (separate p) (show_afs_functions p X))
          (append p (separate p) (show_afs_rewrites p X))).

Fixpoint show_nat
         (n : nat)
  : string
  := match n with
     | 0 => ""
     | S n => String.append "|" (show_nat n)
     end.

Definition string_printer : afs_show string string string string.
Proof.
  simple refine (make_afs_show _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
  - exact "Types".
  - exact "Terms".
  - exact "Rewrite rules".
  - exact String.append.
  - exact "(".
  - exact ")".
  - exact "\n".
  - exact "".
  - exact ":".
  - exact show_nat.
  - exact (fun s => s).
  - exact " -> ".
  - exact (fun s => s).
  - exact (fun s => s).
  - exact "̈\\".
  - exact ".".
  - exact " ".
  - exact "~>".
Defined.
