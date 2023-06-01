Require Import Nijn.Nijn.
Open Scope poly_scope.

Inductive base_types :=
| Ca
| Cb.

Global Instance decEq_base_types : decEq base_types.
Proof.
decEq_finite.
Defined.

Definition a :=
Base Ca.
Definition b :=
Base Cb.

Inductive fun_symbols :=
| Ttt
| Tff
| Tse
| Tuntil.
Global Instance decEq_fun_symbols : decEq fun_symbols.
Proof.
decEq_finite.
Defined.

Definition fn_arity fn_symbols :=
match fn_symbols with
  | Ttt  =>  b
  | Tff  =>  b
  | Tse  =>  b ⟶ a ⟶ a ⟶ a
  | Tuntil => (a ⟶ b) ⟶ (a ⟶ a) ⟶ a ⟶ a
end.

Definition tt {C} : tm fn_arity C _ :=
BaseTm Ttt.
Definition ff {C} : tm fn_arity C _ :=
BaseTm Tff.
Definition se {C} : tm fn_arity C _ :=
BaseTm Tse.
Definition until {C} : tm fn_arity C _ :=
BaseTm Tuntil.

Program Definition rule_0 :=
    make_rewrite
    (_ ,, _ ,, ∙) _
    (se · tt ·  V 0 ·  V 1)
     V 0.

     Program Definition rule_1 :=
    make_rewrite
    (_ ,, _ ,, ∙) _
    (se · ff ·  V 0 ·  V 1)
     V 1.

     Program Definition rule_2 :=
    make_rewrite
    (_ ,, _ ,, _ ,, ∙) _
    (until ·  V 0 ·  V 1 ·  V 2)
    (se · ( V 0 ·  V 2) ·  V 2 · (until ·  V 0 ·  V 1 · ( V 1 ·  V 2))).

Definition trs :=
  make_afs
    fn_arity
    (rule_0 :: rule_1 :: rule_2 :: List.nil).

(* NO
We consider the system AotoYamada_05__003.

  Alphabet:

    false : [] --> a
    if : [a * b * b] --> b
    true : [] --> a
    until : [b -> a * b -> b * b] --> b

  Rules:

    if(true, x, y) => x
    if(false, x, y) => y
    until(f, g, x) => if(f x, x, until(f, g, g x))

This AFS is converted to an AFSM simply by replacing all free variables by meta-variables (with arity 0).

It is easy to see that this system is non-terminating:

  until(f, g, x)
    => if(f x, x, until(f, g, g x))
    |> until(f, g, g x)

That is, a term s reduces to a term t which has a subterm that is an instance of the original term. *)
