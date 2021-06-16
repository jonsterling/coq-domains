From Domains Require Import Preamble Preorder Poset Dcpo Sierpinski DcpoExponential.

Context (D : Dcpo.type).

Local Notation Σ := Sierpinski_Σ_canonical_Dcpo.
Definition Path := map Σ D.

Lemma lub_intro (A : Family Σ): ∀ u ϕ, is_lub A ϕ → A u → ϕ.
Proof. by move=> u ϕ ϕlub; apply: (lub_is_ub A). Qed.

Section PathFromLt.
  Context (x y : D) (xy : x ≤ y).

  Section Family.
    Context (ϕ : Σ).

    Definition path_fam : Family D.
    Proof.
      exists (sum ϕ True).
      by case=> _; [exact: y| exact: x].
    Defined.

    Lemma path_fam_directed : is_directed path_fam.
    Proof.
      split.
      - by exists (inr I).
      - case=>a1; case=>a2 /=.
        + by exists (inl a1).
        + by exists (inl a1).
        + by exists (inl a2).
        + by exists (inr a2).
    Qed.
  End Family.

  Lemma dlub_continuous : is_continuous (λ ϕ : Σ, dlub (path_fam ϕ) (path_fam_directed ϕ)).
  Proof.
    move=> A dirA; split.
    - move=> //= u; apply: (above_lub _)=>//=; case.
      + move=>s; apply: ltT'.
        * by apply: dlub_is_ub; left; apply: (Σ_lub_intro A _ _ _ s).
        * by [].
      + move=> _; apply: ltT'.
        * by apply: dlub_is_ub; right.
        * by [].
    - move=> z zub; apply: (lub_univ _)=>//; case=>/=.
      + move=> h.
        suff: ∃ i, A i.
        * move=> [i u].
          apply: ltT; last by apply: zub.
          apply: ltT'.
          -- apply: lub_is_ub; first by apply: dlub_is_lub.
             by left.
          -- by [].
        * apply: (lub_univ A); first by apply: dlub_is_lub.
          -- by apply/lub_is_ub/Σ_exists_is_lub.
          -- by [].
      + move=> _.
        case: dirA => [[i _] h].
        apply: ltT; last by apply: zub.
        apply: ltT'.
        * by apply: dlub_is_ub; right.
        * by [].
  Qed.

  Definition make_path : Path.
  Proof.
    unshelve esplit.
    - move=> ϕ.
      by apply/dlub/path_fam_directed/ϕ.
    - by apply: dlub_continuous.
  Defined.
End PathFromLt.


Definition HasPath x y := ∃ p : Path, ap p ⊥ = x /\ ap p ⊤ = y.
Infix "⟿" := HasPath (at level 10).

Lemma fwd : ∀ x y : D, x ≤ y → x ⟿ y.
Proof.
  move=> x y xy.
  exists (make_path x y xy); split=>/=.
  - apply: (lub_unique (path_fam _ _ _))=>//; split.
    + by case=>//; rewrite Σ_bot_rw.
    + move=> z h; apply: ltT'.
      * by apply: h; right.
      * by [].
  - apply:  (lub_unique (path_fam _ _ _))=>//; split; first by case.
    move=> z h; apply: ltT'.
    * by apply: h; left; rewrite Σ_top_rw.
    * by [].
Qed.

Lemma bwd : ∀ x y : D, x ⟿ y → x ≤ y.
Proof.
  move=> x y [α [<- <-]].
  by apply: continuous_to_monotone; [apply: ap_cont | apply: bottom_is_bottom].
Qed.

Lemma characterization : ∀ x y, (x ≤ y) = (x ⟿ y).
Proof.
  move=> x y.
  by apply: propext; split; [apply: fwd | apply: bwd].
Qed.
