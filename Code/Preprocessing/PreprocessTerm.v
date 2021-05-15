Require Import Prelude.Basics.
Require Import Preprocessing.TypeChecker.
Require Import List.

(** * Named terms *)

(**
The parser takes terms with named variables as input.
Here we define such terms and we show how to map these to terms with De Bruijn indices.
 *)
Inductive rawNf (V F : Type) : Type :=
| RawNeToNf : rawNe V F -> rawNf V F
| RawNfLam : V -> rawNf V F -> rawNf V F
with rawNe (V F : Type) : Type :=
| RawNeVar : V -> rawNe V F
| RawNeBase : F -> rawNe V F
| RawNeApp : rawNe V F -> rawNf V F -> rawNe V F.

Arguments RawNeToNf {_ _} _.
Arguments RawNfLam {_ _} _ _.
Arguments RawNeVar {_ _} _.
Arguments RawNeBase {_ _} _.
Arguments RawNeApp {_ _} _ _.

(** Removing an element from the list *)
Fixpoint remove
         {A : Type}
         `{decEq A}
         (l : list A)
         (a : A)
  : list A
  := match l with
     | nil => nil
     | x :: xs =>
       match dec_eq x a with
       | Yes _ => remove xs a
       | No _ => x :: remove xs a
       end
     end.

(** The free variables *)
Fixpoint freeVarsNf
         {V F : Type}
         `{decEq V}
         (t : rawNf V F)
  : list V
  := match t with
     | RawNeToNf t => freeVarsNe t
     | RawNfLam a t => remove (freeVarsNf t) a
     end
with freeVarsNe
     {V F : Type}
     `{decEq V}
     (t : rawNe V F)
  : list V
  := match t with
     | RawNeVar a => a :: nil
     | RawNeBase b => nil
     | RawNeApp t1 t2 => freeVarsNe t1 ++ freeVarsNf t2
     end.

(** Take the index of a variable *)
Fixpoint rawVarToUtVar
         {V : Type}
         `{decEq V}
         (vs : list V)
         (x : V)
  : option utVar
  := match vs with
     | nil => None
     | v :: vs =>
       match dec_eq x v with
       | Yes _ => Some VzUt
       | No _ =>
         match rawVarToUtVar vs x with
         | Some v' => Some (VsUt v')
         | None => None
         end
       end
     end.

(** Go from terms with named variables to terms with De Bruijn indices *)
Fixpoint rawNfToUtNf_vars
         {V F : Type}
         `{decEq V}
         (vs : list V)
         (t : rawNf V F)
  : option (utNf F)
  := match t with
     | RawNeToNf t =>
       match rawNeToUtNe_vars vs t with
       | Some t' => Some (UtNeToNf t')
       | None => None
       end
     | RawNfLam a t => rawNfToUtNf_vars (a :: vs) t
     end
with rawNeToUtNe_vars
     {V F : Type}
     `{decEq V}
     (vs : list V)
     (t : rawNe V F)
  : option (utNe F)
  := match t with
     | RawNeVar v =>
       match rawVarToUtVar vs v with
       | Some t => Some (UtNeVar t)
       | None => None
       end
     | RawNeBase f => Some (UtNeBase f)
     | RawNeApp t1 t2 =>
       match rawNeToUtNe_vars vs t1 , rawNfToUtNf_vars vs t2 with
       | Some t1 , Some t2 => Some (UtNeApp t1 t2)
       | _ , _ => None
       end
     end.

Definition rawNfToUtNf
           {V F : Type}
           `{decEq V}
           (t : rawNf V F)
  : option (utNf F)
  := rawNfToUtNf_vars (freeVarsNf t) t.

Definition rawNfToUtNe
           {V F : Type}
           `{decEq V}
           (t : rawNe V F)
  : option (utNe F)
  := rawNeToUtNe_vars (freeVarsNe t) t.
