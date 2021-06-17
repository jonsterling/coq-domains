From Domains Require Import Preamble.

Declare Scope preorder_scope.
Delimit Scope preorder_scope with P.

Open Scope preorder_scope.

HB.mixin Record PreorderOfType A :=
  {lt : A → A → Prop;
   ltR : ∀ x, lt x x;
   ltT : ∀ x y z, lt x y → lt y z → lt x z}.

HB.structure Definition Preorder := {A of PreorderOfType A}.

Lemma ltT' {A : Preorder.type} : ∀ x y z : A, lt y z → lt x y → lt x z.
Proof. by move=>???/[swap]; exact: ltT. Qed.

Infix "≤" := lt : preorder_scope.
