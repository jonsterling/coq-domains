Require Import Preamble Preorder Poset Dcpo.

Definition Σ := Prop.
Definition Σ_lt (x y : Σ) := x → y.

Lemma Σ_ltR : ∀ x : Σ, x → x.
Proof. auto. Qed.

Lemma Σ_ltT : ∀ x y z : Σ, (x → y) → (y → z) → x → z.
Proof. auto. Qed.

HB.instance Definition Σ_preorder_axioms := PreorderOfType.Build Σ Σ_lt Σ_ltR Σ_ltT.

Lemma Σ_ltE : ∀ x y : Σ, (x ≤ y) → (y ≤ x) → x = y.
Proof. move=> *; apply: propositional_extensionality; by split. Qed.

HB.instance Definition Σ_poset_axioms := PosetOfPreorder.Build Σ Σ_ltE.

Lemma Σ_ltHasDLubs : ∀ (A : Family Σ), is_directed A → ∃ x, is_lub A x.
Proof.
  move=> A dir //=.
  exists (∃ x, A x).
  split; simpl.
  - by compute; eauto.
  - move=> z zub; move=> [? ?].
      by apply: zub; eauto.
Qed.

HB.instance Definition Σ_dcpo_axioms := DcpoOfPoset.Build Σ Σ_ltHasDLubs.

Lemma Σ_ltHasBot : ∃ x : Σ, is_bottom x.
Proof. exists False; by move=> ?. Qed.

Lemma Σ_ltHasTop : ∃ x : Σ, is_top x.
Proof. exists True; by move=> ?. Qed.

HB.instance Definition Σ_pointed_poset_axioms := PointedPosetOfPoset.Build Σ Σ_ltHasBot.
HB.instance Definition Σ_bounded_poset_axioms := BoundedPosetOfPointedPoset.Build Σ Σ_ltHasTop.
