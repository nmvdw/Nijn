Require Import Nijn.Prelude.
Require Import Nijn.Syntax.
Require Import Nijn.Interpretation.OrderInterpretation.
Require Import Nijn.TerminationTechniques.PolynomialMethod.Polynomial.
Require Import Lia.
Require Import PeanoNat.
Import Nat.
Require Import List.

Open Scope nat.

(** * A tactic to check the constraints coming from the polynomial interpretation *)

(** ** Generating goals *)
(** An AFS comes with a list of rewrite rules. As such, if we need to prove something for every rewrite rule, we start with an assumption that we have a rewrite rule that is a member of the list of rewrite rules. This tactic destructs this goal so that we have a goal for every rewrite rule. In each of those goals, the goal is simplified *)
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

(** ** Solving inequalities *)
(** We also need to solve inequalities that involve some weakly monotonic map. This tactic solves such goals. It gets an assumption which is the proof of monotonicity *)
Ltac solve_ineq Hf := subst ; apply Hf ; cbn ; nia.

(** ** Simplifiying contexts *)
(** For every rewrite rule, we have a variable in the context. The type of this variable, let's call it `x`,is the interpretation of some context. As such, the type of `x` is some product, and this tactic destructs `x` so that we don't have products/unit ty[es in the context. *)
Ltac destruct_con :=
  repeat (match goal with
          | [ x : _ * _ |- _ ] => destruct x
          | [ x : unit |- _ ] => destruct x
          end) ;
  cbn -[add mul] in *.

(** ** Generating names *)
(** The goal we have is some inequality that might involve variables that are function types. Each instance of this function will be fully applied. To aid the usage of `nia`, we replace all of these occurences by variable of type natural numbers together with an assumption that they are equal to the function applied to some variable. *)
Ltac generate_vars f :=
  repeat (match goal with
          | |- context G [f ?z] => let w := fresh "w" in remember (f z) as w
          end).

(** ** Generating inequality goals *)
(** This tactic generates an assumption `x >= y` for every pair of variables whose type are natural numbers in the context, which can be proven using `solve_ineq`. Its argument is a proof of weak monotonicity of some function `f`, and that one will be used for solving all inequalities. *)
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

(** ** Destructing weakly monotone maps *)
(** For every variable in the context that is a weakly monotonic map, assumptions are generated. First, every occurence of the weakly monotonic map in the goal are generated and then inequalities are generated. *)
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

(** ** Solving polynomial goals *)
(** This tactic tries to prove strong normalization using the polynomial method. Its argument is a polynomial for every function symbol of the system. It applies the theorems, and after that, it used the tactics we discussed before. So, it first generates the goals and then it destructs the context. After that it tries to generate as many assumptions as possible, and then `nia` is used. *)
Ltac solve_poly pols :=
  apply afs_is_SN_from_Interpretation ;
  apply (poly_Interpretation _ pols) ;
  generate_goals ;
  (destruct_con ; destruct_WM ; nia).
