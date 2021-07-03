Require Import Basics.
Require Import List.

Declare Scope error.

Inductive error (A : Type) : Type :=
| Ret : A -> error A
| TypeCheckErrorNoVar : error A
| TypeCheckErrorNoBase : error A
| TypeCheckErrorOther : error A
| ScopeError : error A
| UndefinedSymbol : error A.

Arguments Ret {_} _.
Arguments TypeCheckErrorNoVar {_}.
Arguments TypeCheckErrorNoBase {_}.
Arguments TypeCheckErrorOther {_}.
Arguments ScopeError {_}.
Arguments UndefinedSymbol {_}.

Definition error_return
           (A : Type)
  : A -> error A
  := Ret.

Definition error_map
           {A B : Type}
           (f : A -> B)
           (x : error A)
  : error B
  := match x with
     | Ret a => Ret (f a)
     | TypeCheckErrorNoVar => TypeCheckErrorNoVar
     | TypeCheckErrorNoBase => TypeCheckErrorNoBase
     | TypeCheckErrorOther => TypeCheckErrorOther
     | ScopeError => ScopeError
     | UndefinedSymbol => UndefinedSymbol
     end.

Definition error_bind
           {A B : Type}
           (x : error A)
           (f : A -> error B)
  : error B
  := match x with
     | Ret a => f a
     | TypeCheckErrorNoVar => TypeCheckErrorNoVar
     | TypeCheckErrorNoBase => TypeCheckErrorNoBase
     | TypeCheckErrorOther => TypeCheckErrorOther
     | ScopeError => ScopeError
     | UndefinedSymbol => UndefinedSymbol
     end.

Notation "x >>= f" := (error_bind x f) : error.

Local Open Scope error.

Fixpoint list_error
         {A : Type}
         (l : list (error A))
  : error (list A)
  := match l with
     | nil => Ret nil
     | x :: xs =>
       list_error xs >>= fun ys => x >>= fun y => Ret (y :: ys)
     end.
