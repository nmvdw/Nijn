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

Import AFSNotation.

Definition no_left
  : tm trs (a ⟶ b ,, a ,, ∙) a
  := let f := TmVar Vz in
     let x := TmVar (Vs Vz) in
     until · f · (λ TmVar Vz) · x.

Definition no_right
  : tm trs (a ⟶ b ,, a ,, ∙) a
  := let f := TmVar Vz in
     let x := TmVar (Vs Vz) in
     se · (f · x) · x · (until · f · (λ TmVar Vz) · x).

Definition paard
  : no_left ≼ no_right.
Proof.
  apply SubAppR.
  apply subTm_refl.
Qed.

Definition no_red
  : no_left ∼> no_right.
Proof.
  unfold no_left, no_right.
(*
  trans
  {
    find place
    apply rule
  }
  cbn
  trans
  {
    find place
    apply rule
  }
  cbn
  trans
  {
    find place
    apply rule
  }
  cbn
  trans
  {
    find place
    apply rule
  }
  cbn
  trans
  {
    find place
    apply rule
  }
  cbn
  fihd place
  apply rule
 *)
  refine (rew_Trans _ _).
  {
    refine (rew_rewrite_rule
              trs
              (MakeMem rule_2 _)
              (ToEmpty _ && _ && _ && _)).
    solve_In.
  }
  cbn.
  apply rew_App_r.
  apply rew_App_r.
  apply rew_betaRed.
Qed.

Theorem koe
  : ~(isSN trs).
Proof.
  apply inc_loop_to_notSN.
  apply (Build_inc_loop
           trs
           _ _
           no_left
           no_right
           no_red).
  apply paard.


Theorem inc_loop_to_notSN
          (l : inc_loop)
    : ~(isSN X).


(* No
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
