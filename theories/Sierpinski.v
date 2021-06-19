From Domains Require Import Preamble Preorder Poset Dcpo.

Definition Σ := Prop.
Definition Σ_lt (x y : Σ) := x → y.

Lemma Σ_ltR : ∀ x : Σ, x → x.
Proof. by []. Qed.

Lemma Σ_ltT : ∀ x y z : Σ, (x → y) → (y → z) → x → z.
Proof. by move=>???/[swap]; exact: comp. Qed.

HB.instance Definition Σ_preorder_axioms := PreorderOfType.Build Σ Σ_lt Σ_ltR Σ_ltT.

Lemma Σ_ltE : ∀ x y : Σ, (x ≤ y) → (y ≤ x) → x = y.
Proof. by move=> *; apply: propext. Qed.

HB.instance Definition Σ_poset_axioms := PosetOfPreorder.Build Σ Σ_ltE.

Lemma Σ_exists_is_lub : ∀ (A : Family Σ), is_lub A (∃ x, A x).
Proof.
  move=> A; split=>/=.
  - by move=>i; move=>?; exists i.
  - move=>? zub; move=> [x ?].
    by apply: (zub x).
Qed.

Lemma Σ_ltHasDLubs : ∀ (A : Family Σ), is_directed A → ∃ x, is_lub A x.
Proof.
  move=> A dir //=.
  exists (∃ x, A x).
  by apply: Σ_exists_is_lub.
Qed.

HB.instance Definition Σ_dcpo_axioms := DcpoOfPoset.Build Σ Σ_ltHasDLubs.

Lemma Σ_ltHasBot : ∃ x : Σ, is_bottom x.
Proof. by exists False=>?. Qed.

Lemma Σ_ltHasTop : ∃ x : Σ, is_top x.
Proof. by exists True=>?. Qed.

HB.instance Definition Σ_pointed_poset_axioms := PointedPosetOfPoset.Build Σ Σ_ltHasBot.
HB.instance Definition Σ_bounded_poset_axioms := BoundedPosetOfPointedPoset.Build Σ Σ_ltHasTop.

Lemma Σ_top_rw : (⊤ : Σ) = True.
Proof.
  apply: top_is_unique=>//=.
  by apply: top_is_top.
Qed.

Lemma Σ_bot_rw : (⊥ : Σ) = False.
Proof.
  apply: bottom_is_unique.
  - by apply: bottom_is_bottom.
  - by move=>?.
Qed.

Lemma Σ_lub_intro (A : Family Σ): ∀ u ϕ, is_lub A ϕ → A u → ϕ.
Proof. by move=> ???; apply: (lub_is_ub A). Qed.

Lemma Σ_lub_elim {P Q: Σ} {A} : is_lub A P → (∀ x, A x → Q) → P → Q.
Proof.
  move=> H J.
  rewrite -(lub_unique _ _ _ (Σ_exists_is_lub _) H).
  by case; apply: J.
Qed.
