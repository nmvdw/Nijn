Require Import Prelude.Basics.
Require Import Syntax.Signature.
Require Import Syntax.StrongNormalization.BetaNormalForm.
Require Import Preprocessing.Error.

(** * The type checker *)

(** ** Untyped normal forms *)
Inductive utVar : Type :=
| VzUt : utVar
| VsUt : utVar -> utVar.

Inductive utNf (F : Type) : Type :=
| UtNeToNf : utNe F -> utNf F
| UtNfLam : utNf F -> utNf F
with utNe (F : Type) : Type :=
| UtNeVar : utVar -> utNe F
| UtNeBase : F -> utNe F
| UtNeApp : utNe F -> utNf F -> utNe F.

Arguments UtNeToNf {_} _.
Arguments UtNfLam {_} _.
Arguments UtNeVar {_} _.
Arguments UtNeBase {_} _.
Arguments UtNeApp {_} _ _.

(** Each typed normal form gives an untyped normal form *)
Fixpoint varToUtVar
         {B : Type}
         {C : con B}
         {A : ty B}
         (v : var C A)
  : utVar
  := match v with
     | Vz => VzUt
     | Vs v => VsUt (varToUtVar v)
     end.        

Fixpoint nfToUtNf
         {B : Type}
         {F : Type}
         {C : con B}
         {ar : F -> ty B}
         {A : ty B}
         (t : nf ar C A)
  : utNf F
  := match t with
     | NeToNf t => UtNeToNf (neToUtNe t)
     | NfLam t => UtNfLam (nfToUtNf t)
     end
with neToUtNe
     {B : Type}
     {F : Type}
     {C : con B}
     {ar : F -> ty B}
     {A : ty B}
     (t : ne ar C A)
  : utNe F
  := match t with
     | NeVar v => UtNeVar (varToUtVar v)
     | NeBaseTm f => UtNeBase f
     | NeApp f t => UtNeApp (neToUtNe f) (nfToUtNf t)
     end.

(** ** Derivations *)
Inductive derivation_Var {B : Type} : con B -> ty B -> utVar -> Type :=
| TypeVz : forall (C : con B) (A : ty B), derivation_Var (A ,, C) A VzUt
| TypeVs : forall (C : con B) (A1 A2 : ty B) (v : utVar),
    derivation_Var C A2 v -> derivation_Var (A1 ,, C) A2 (VsUt v).

Arguments TypeVz {_ _ _}.
Arguments TypeVs {_ _ _ _ _} _.

Inductive derivation_Nf
          {B : Type}
          {F : Type}
          (C : con B)
          (ar : F -> ty B)
  : ty B -> utNf F -> Type
  :=
| TypeNe : forall (A : ty B) (t : utNe F),
    derivation_Ne C ar A t
    ->
    derivation_Nf C ar A (UtNeToNf t)
| TypeLam : forall {A1 A2 : ty B} (f : utNf F),
    derivation_Nf (A1 ,, C) ar A2 f
    ->
    derivation_Nf C ar (A1 ⟶ A2) (UtNfLam f)
with derivation_Ne
     {B : Type}
     {F : Type}
     (C : con B)
     (ar : F -> ty B)
  : ty B -> utNe F -> Type
  :=
| TypeVar : forall (A : ty B) (v : utVar),
    derivation_Var C A v
    ->
    derivation_Ne C ar A (UtNeVar v)
| TypeBase : forall (f : F), derivation_Ne C ar (ar f) (UtNeBase f)
| TypeApp : forall {A1 A2 : ty B}
                   (f : utNe F)
                   (t : utNf F),
    derivation_Ne C ar (A1 ⟶ A2) f
    ->
    derivation_Nf C ar A1 t
    ->
    derivation_Ne C ar A2 (UtNeApp f t).

Arguments TypeNe {_ _ _ _ _ _} _.
Arguments TypeLam {_ _ _ _ _ _ _} _.
Arguments TypeVar {_ _ _ _ _ _} _.
Arguments TypeBase {_ _ _ _} _.
Arguments TypeApp {_ _ _ _ _ _ _ _} _ _.

(** The derivation given by a typed normal form *)
Fixpoint varToUtVar_derivation
         {B : Type}
         {C : con B}
         {A : ty B}
         (v : var C A)
  : derivation_Var C A (varToUtVar v)
  := match v with
     | Vz => TypeVz
     | Vs v => TypeVs (varToUtVar_derivation v)
     end.

Fixpoint nfToUtNf_derivation
         {B : Type}
         {F : Type}
         {C : con B}
         {ar : F -> ty B}
         {A : ty B}
         (t : nf ar C A)
  : derivation_Nf C ar A (nfToUtNf t)
  := match t with
     | NeToNf t => TypeNe (neToUtNe_derivation t)
     | NfLam t => TypeLam (nfToUtNf_derivation t)
     end
with neToUtNe_derivation
     {B : Type}
     {F : Type}
     {C : con B}
     {ar : F -> ty B}
     {A : ty B}
     (t : ne ar C A)
  : derivation_Ne C ar A (neToUtNe t)
  := match t with 
     | NeVar v => TypeVar (varToUtVar_derivation v)
     | NeBaseTm f => TypeBase f
     | NeApp f t => TypeApp (neToUtNe_derivation f) (nfToUtNf_derivation t)
     end.

(** From derivations to well-typed terms *)
Fixpoint derivation_to_var
         {B : Type}
         {C : con B}
         {A : ty B}
         {v : utVar}
         (Hv : derivation_Var C A v)
  : var C A
  := match Hv with
     | TypeVz => Vz
     | TypeVs d => Vs (derivation_to_var d)
     end.

Fixpoint derivation_to_nf
         {B : Type}
         {F : Type}
         {C : con B}
         {ar : F -> ty B}
         {A : ty B}
         {t : utNf F}
         (Ht : derivation_Nf C ar A t)
  : nf ar C A
  := match Ht with
     | TypeNe d => NeToNf (derivation_to_ne d)
     | TypeLam d => NfLam (derivation_to_nf d)
     end
with derivation_to_ne
     {B : Type}
     {F : Type}
     {C : con B}
     {ar : F -> ty B}
     {A : ty B}
     {t : utNe F}
     (Ht : derivation_Ne C ar A t)
  : ne ar C A
  := match Ht with
     | TypeVar v => NeVar (derivation_to_var v)
     | TypeBase f => NeBaseTm f
     | TypeApp d1 d2 => NeApp (derivation_to_ne d1) (derivation_to_nf d2)
     end.

(** They are inverses *)
Definition var_to_derivation_to_var
           {B : Type}
           {C : con B}
           {A : ty B}
           (v : var C A)
  : derivation_to_var (varToUtVar_derivation v) = v.
Proof.
  induction v as [ | ? ? ? v IHv ] ; simpl.
  - reflexivity.
  - f_equal.
    apply IHv.
Qed.

Fixpoint nf_to_derivation_to_nf
         {B : Type}
         {F : Type}
         {C : con B}
         {ar : F -> ty B}
         {A : ty B}
         (t : nf ar C A)
  : derivation_to_nf (nfToUtNf_derivation t) = t
with ne_to_derivation_to_ne
     {B : Type}
     {F : Type}
     {C : con B}
     {ar : F -> ty B}
     {A : ty B}
     (t : ne ar C A)
  : derivation_to_ne (neToUtNe_derivation t) = t.
Proof.
  - destruct t ; simpl ; f_equal.
    + apply ne_to_derivation_to_ne.
    + apply nf_to_derivation_to_nf.
  - destruct t ; simpl ; f_equal.
    + apply var_to_derivation_to_var.
    + apply ne_to_derivation_to_ne.
    + apply nf_to_derivation_to_nf.
Qed.

Definition derivation_to_var_to_derivation
           {B : Type}
           {C : con B}
           {A : ty B}
           {v : utVar}
           (Hv : derivation_Var C A v)
  : varToUtVar (derivation_to_var Hv) = v.
Proof.
  induction Hv as [ | ? ? ? ? Hv IHv ] ; simpl.
  - reflexivity.
  - f_equal.
    apply IHv.
Qed.

Fixpoint derivation_to_nf_to_derivation
         {B : Type}
         {F : Type}
         {C : con B}
         {ar : F -> ty B}
         {A : ty B}
         {t : utNf F}
         (Ht : derivation_Nf C ar A t)
  : nfToUtNf (derivation_to_nf Ht) = t
with derivation_to_ne_to_derivation
     {B : Type}
     {F : Type}
     {C : con B}
     {ar : F -> ty B}
     {A : ty B}
     {t : utNe F}
     (Ht : derivation_Ne C ar A t)
  : neToUtNe (derivation_to_ne Ht) = t.
Proof.
  - destruct Ht ; simpl ; f_equal.
    + apply derivation_to_ne_to_derivation.
    + apply derivation_to_nf_to_derivation.
  - destruct Ht ; simpl ; f_equal.
    + apply derivation_to_var_to_derivation.
    + apply derivation_to_ne_to_derivation.
    + apply derivation_to_nf_to_derivation.
Qed.

(** ** Type inference and type checking *)

(** We use fhe following abbreivation *)
Notation "( a , b )" := (existT _ a b).

(** To guarantee soundness, a derivation is computed by the function *)
Fixpoint inferVar
         {B : Type}
         (C : con B)
         (v : utVar)
  : error { A : ty B & derivation_Var C A v }
  := match C , v with
     | ∙ , _ => TypeCheckErrorNoVar
     | A ,, C , VzUt => Ret (A , TypeVz)
     | A ,, C , VsUt v =>
       match inferVar C v with
       | Ret (A , d) => Ret (A , TypeVs d)
       | TypeCheckErrorNoVar => TypeCheckErrorNoVar
       | TypeCheckErrorNoBase => TypeCheckErrorNoBase
       | TypeCheckErrorOther => TypeCheckErrorOther
       | ScopeError => ScopeError
       | UndefinedSymbol => UndefinedSymbol
       end
     end.

Fixpoint check
         {B : Type}
         `{decEq B}
         {F : Type}
         (C : con B)
         (ar : F -> ty B)
         (t : utNf F)
         (A : ty B)
  : error (derivation_Nf C ar A t)
  := match t with
     | UtNeToNf t =>
       match infer C ar t with
       | Ret z =>
         match dec_eq (projT1 z) A with
         | Yes p => Ret (TypeNe (transport (fun z => derivation_Ne C ar z _) p (projT2 z)))
         | No _ => TypeCheckErrorOther
         end
     | TypeCheckErrorNoVar => TypeCheckErrorNoVar
     | TypeCheckErrorNoBase => TypeCheckErrorNoBase
     | TypeCheckErrorOther => TypeCheckErrorOther
       | ScopeError => ScopeError
       | UndefinedSymbol => UndefinedSymbol
       end
     | UtNfLam t =>
       match A with
       | Base _ => TypeCheckErrorOther
       | A1 ⟶ A2 => error_map TypeLam (check (A1 ,, C) ar t A2)
       end
     end
with infer
     {B : Type}
     `{decEq B}
     {F : Type}
     (C : con B)
     (ar : F -> ty B)
     (t : utNe F)
  : error { A : ty B & derivation_Ne C ar A t }
  := match t with
     | UtNeVar v =>
       match inferVar C v with
       | Ret (A , d) => Ret (A , TypeVar d)
       | TypeCheckErrorNoVar => TypeCheckErrorNoVar
       | TypeCheckErrorNoBase => TypeCheckErrorNoBase
       | TypeCheckErrorOther => TypeCheckErrorOther
       | ScopeError => ScopeError
       | UndefinedSymbol => UndefinedSymbol
       end
     | UtNeBase f => Ret (ar f , TypeBase f)
     | UtNeApp f t =>
       match infer C ar f with
       | Ret (Base _ , n) => TypeCheckErrorOther
       | Ret (A1 ⟶ A2 , n) => error_map (fun m => (A2 , TypeApp n m)) (check C ar t A1)
       | TypeCheckErrorNoVar => TypeCheckErrorNoVar
       | TypeCheckErrorNoBase => TypeCheckErrorNoBase
       | TypeCheckErrorOther => TypeCheckErrorOther
       | ScopeError => ScopeError
       | UndefinedSymbol => UndefinedSymbol
       end
     end.

Definition infer_var_complete
           {B : Type}
           {C : con B}
           {v : utVar}
           {A : ty B}
           (d : derivation_Var C A v)
  : inferVar C v = Ret (A , d).
Proof.
  induction d as [ | ? ? ? ? d IHd ] ; simpl.
  - reflexivity.
  - rewrite IHd.
    simpl.
    reflexivity.
Qed.

Fixpoint check_complete
         {B : Type}
         `{decEq B}
         {F : Type}
         {C : con B}
         {ar : F -> ty B}
         {A : ty B}
         {t : utNf F}
         (Ht : derivation_Nf C ar A t)
  : check C ar t A = Ret Ht
with infer_complete
     {B : Type}
     `{decEq B}
     {F : Type}
     {C : con B}
     {ar : F -> ty B}
     {A : ty B}
     {t : utNe F}
     (Ht : derivation_Ne C ar A t)
  : infer C ar t = Ret (A , Ht).
Proof.
  - destruct Ht as [ ? ? d | ? ? ? d ] ; simpl.
    + rewrite (infer_complete _ _ _ _ _ _ _ d).
      simpl.
      destruct (dec_eq_Ty A A) ; try contradiction.
      rewrite (hedberg e (eq_refl _)).
      reflexivity.
    + rewrite (check_complete _ _ _ _ _ _ _ d).
      reflexivity.
  - destruct Ht as [ ? v d | | ? ? ? ? d1 d2 ] ; simpl.
    + rewrite (infer_var_complete d).
      reflexivity.
    + reflexivity.
    + rewrite (infer_complete _ _ _ _ _ _ _ d1).
      simpl.
      rewrite (check_complete _ _ _ _ _ _ _ d2).
      reflexivity.
Qed.

(** ** Going from untyped terms to well-typed terms *)
Definition check_to_tm
           {B : Type}
           `{decEq B}
           {F : Type}
           (C : con B)
           (ar : F -> ty B)
           (t : utNf F)
           (A : ty B)
  : error (tm ar C A)
  := error_map (fun z => nfToTm (derivation_to_nf z)) (check C ar t A).

Definition infer_to_tm
           {B : Type}
           `{decEq B}
           {F : Type}
           (C : con B)
           (ar : F -> ty B)
           (t : utNe F)
  : error { A : ty B & tm ar C A }
  := error_map
       (fun z => (projT1 z , neToTm (derivation_to_ne (projT2 z))))
       (infer C ar t).
