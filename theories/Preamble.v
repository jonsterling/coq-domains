Require Export ssreflect ssrfun Unicode.Utf8.
From HB Require Export structures.
Require Export Coq.Logic.Description Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality Program.Equality.

Set Primitive Projections.

Definition iota {X : Type} (P : X → Prop) (h : exists! x, P x) : X :=
  proj1_sig (constructive_definite_description _ h).

Lemma iota_prop {X : Type} (P : X → Prop) (h : exists! x, P x) : P (iota P h).
Proof. rewrite /iota; apply proj2_sig. Qed.

Definition extract {X : Type} {P : X → Prop} : (∀ x y, P x → P y → x = y) → (∃ x, P x) → X.
Proof.
  move=> H J.
  apply: (@iota X P).
  case: J=> x xP.
  exists x; split; first by [].
  by move=> ??; apply: H.
Defined.

Definition extract_prop {X : Type} {P : X → Prop} : ∀ H J, P (@extract X P H J).
Proof.
  move=> ? ?.
  apply: iota_prop.
Qed.

Opaque extract.

Module Im.
  Section Im.
    Context {X Y : Type} (f : X → Y).

    Definition T : Type :=
      { y : Y | ∃ x, f x = y }.

    Definition surj : X → T.
    Proof. by move=> x; exists (f x); exists x. Defined.

    Definition inj : T → Y.
    Proof. by apply: proj1_sig. Defined.

    Lemma inj_injective : ∀ x y, inj x = inj y → x = y.
    Proof. by move=> x y h; apply/eq_sig/proof_irrelevance. Qed.

    Lemma surj_surjective : ∀ i : T, ∃ x : X, surj x = i.
    Proof. by move=> [y [x h]]; exists x; apply/eq_sig/proof_irrelevance. Qed.
  End Im.
End Im.

Notation Im := Im.T.

Notation propext := propositional_extensionality.
Notation funext := functional_extensionality.
Notation proofirr := proof_irrelevance.

#[global]
Hint Resolve proofirr : core.
