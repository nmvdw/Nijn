Require Import Lia.
Require Import PeanoNat.
Import Nat.
Require Import List.
Require Import Prelude.Basics.
Require Import Prelude.Orders.
Require Import Syntax.Signature.
Require Import Interpretation.Polynomial.
Require Import Interpretation.WeaklyMonotonicAlgebra.

Open Scope nat.

Ltac generate_goals :=
  intros ; 
  unfold rewriteRules in * ;
  match goal with
  | [ x : members _ |- _ ] => destruct x
  end ;
  repeat (match goal with
          | [ x : In _ _ |- _ ] => destruct x
          end) ;
  subst ; cbn -[add mul] in *.

Ltac solve_ineq Hf := subst ; apply Hf ; cbn ; nia.

Ltac destruct_con :=
  repeat (match goal with
          | [ x : _ * _ |- _ ] => destruct x
          | [ x : unit |- _ ] => destruct x
          end) ;
  cbn -[add mul] in *.
Ltac generate_vars f :=
  repeat (match goal with
          | |- context G [f ?z] => let w := fresh "w" in remember (f z) as w
          end).

Ltac NotFound a l :=
 let rec find l :=
   lazymatch l with
   | nil     => idtac
   | a :: _  => fail "Found"
   | _ :: ?l => find l
   end
 in find l.
Ltac generate_ineqs Hf :=
  let rec go acc :=
    match goal with
    | [ N : nat, M : nat |- _ ] =>
        NotFound (N,M) acc;
        try (assert (N >= M) by solve_ineq Hf) ;
        go ((N,M)::acc)
    | _ => idtac
    end
  in go (@nil (nat * nat)).

Ltac destruct_WM :=
  repeat (match goal with
          | [ g : weakMonotoneMap _ _ |- _ ] =>
              let f := fresh "f" in
              let Hf := fresh "Hf" in
              destruct g as [ f Hf ] ;
              cbn -[add mul] in * ;
              generate_vars f ;
              generate_ineqs Hf
          end).
Ltac solve_poly pols :=
  apply afs_is_SN_from_Alg ;
  apply (poly_WMalgebra _ pols) ;
  generate_goals ;
  (destruct_con ; destruct_WM ; nia).
