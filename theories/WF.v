From Domains Require Import Preamble Preorder Poset.

HB.mixin Record HasWf A of Preorder A :=
  {mem : A → A → Prop;
   memWf : well_founded mem;
   memLt : ∀ u v, mem u v → u ≤ v;
   memT : ∀ u v w, mem u v → mem v w → mem u w;
   memL : ∀ u v w, u ≤ v → mem v w → mem u w;
   memR : ∀ u v w, mem u v → v ≤ w → mem u w}.

HB.structure Definition WfPreorder := {A of HasWf A & Preorder A}.
HB.structure Definition WfPoset := {A of WfPreorder A & Poset A}.

Infix "≺" := mem (at level 60) : preorder_scope.
