Require Export Syntax.Signature.Types.
Require Export Syntax.Signature.Contexts.
Require Export Syntax.Signature.Terms.

Definition test
           {B : Type}
           (C : Con B)
           (A : Ty B)
           {F : Type}
           (ar : F -> Ty B)
  : Tm ar C (A ⟶ A)
  := λ (TmVar Vz).

Require Import Extraction.

Extraction Language Haskell.

Separate Extraction test.
