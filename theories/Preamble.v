Require Export ssreflect Unicode.Utf8.
From HB Require Export structures.
Require Export Coq.Logic.Description Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality Program.Equality.

Set Primitive Projections.

Definition iota {X : Type} (P : X → Prop) (h : exists! x, P x) : X :=
  proj1_sig (constructive_definite_description _ h).

Lemma iota_prop {X : Type} (P : X → Prop) (h : exists! x, P x) : P (iota P h).
Proof. rewrite /iota; apply proj2_sig. Qed.


Module Im.
  Section Im.
    Context {X Y : Type} (f : X → Y).

    Definition T : Type :=
      { y : Y | ∃ x, f x = y }.

    Definition surj : X → T.
    Proof. move=> x; exists (f x); by exists x. Defined.

    Definition inj : T → Y.
    Proof. apply: proj1_sig. Defined.

    Lemma inj_injective : ∀ x y, inj x = inj y → x = y.
    Proof. move=> x y h; apply: eq_sig; apply: proof_irrelevance. Qed.

    Lemma surj_surjective : ∀ i : T, ∃ x : X, surj x = i.
    Proof. move=> [y [x h]]; exists x; apply: eq_sig; apply: proof_irrelevance. Qed.
  End Im.
End Im.

Notation Im := Im.T.

Notation propext := propositional_extensionality.
Notation funext := functional_extensionality.
Notation proofirr := proof_irrelevance.

#[global]
Hint Resolve proofirr : core.
