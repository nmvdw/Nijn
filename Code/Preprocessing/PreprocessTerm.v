Require Import Prelude.Basics.
Require Import Preprocessing.Error.
Require Import Preprocessing.TypeChecker.
Require Import List.

Open Scope error.

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
  : error utVar
  := match vs with
     | nil => ScopeError
     | v :: vs =>
       match dec_eq x v with
       | Yes _ => Ret VzUt
       | No _ => error_map VsUt (rawVarToUtVar vs x)
       end
     end.

(** Go from terms with named variables to terms with De Bruijn indices *)
Fixpoint rawNfToUtNf_vars
         {V F : Type}
         `{decEq V}
         (vs : list V)
         (t : rawNf V F)
  : error (utNf F)
  := match t with
     | RawNeToNf t => error_map UtNeToNf (rawNeToUtNe_vars vs t)
     | RawNfLam a t =>
       rawNfToUtNf_vars (a :: vs) t
       >>= fun t1 => Ret (UtNfLam t1)
     end
with rawNeToUtNe_vars
     {V F : Type}
     `{decEq V}
     (vs : list V)
     (t : rawNe V F)
  : error (utNe F)
  := match t with
     | RawNeVar v => error_map UtNeVar (rawVarToUtVar vs v)
     | RawNeBase f => Ret (UtNeBase f)
     | RawNeApp t1 t2 =>
       rawNeToUtNe_vars vs t1
       >>= fun t1 => rawNfToUtNf_vars vs t2
       >>= fun t2 => Ret (UtNeApp t1 t2)
     end.
