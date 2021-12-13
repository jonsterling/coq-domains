From Domains Require Import Preamble Category Preorder Poset Dcpo.

HB.mixin Record FilteredPreorderOfPreorder A of Preorder A :=
  {fp_inh : ∃ x : A, True;
   fp_predir : ∀ x y : A, ∃ z : A, x ≤ z ∧ y ≤ z}.

HB.structure Definition FilteredPreoder := {A of FilteredPreorderOfPreorder A & Preorder A}.
HB.structure Definition FilteredPoset := {A of FilteredPreorderOfPreorder A & Poset A}.
