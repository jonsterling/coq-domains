Require Import Preamble Preorder Poset Dcpo Sierpinski DcpoExponential.

Context (D : Dcpo.type).

Local Notation Σ := Sierpinski_Σ_canonical_Dcpo.
Definition Path := map Σ D.

Lemma lub_intro (A : Family Σ): ∀ u ϕ, is_lub A ϕ → A u → ϕ.
Proof. move=> u ϕ ϕlub; by apply: (lub_is_ub A ϕ ϕlub u). Qed.

Section PathFromLt.
  Context (x y : D) (xy : x ≤ y).

  Section Family.
    Context (ϕ : Σ).

    Definition path_fam : Family D.
    Proof.
      unshelve esplit.
      - refine (sum ϕ True).
      - case=> _.
        + exact: y.
        + exact: x.
    Defined.

    Lemma path_fam_directed : is_directed path_fam.
    Proof.
      split.
      - unshelve esplit; [by right|done].
      - case=> ?; case => ?; cbn.
        + unshelve esplit.
          * by left.
          * done.
        + unshelve esplit.
          * by left.
          * done.
        + unshelve esplit.
          * by left.
          * done.
        + unshelve esplit.
          * by right.
          * done.
    Qed.
  End Family.

  Lemma dlub_continuous : is_continuous (λ ϕ : Σ, dlub (path_fam ϕ) (path_fam_directed ϕ)).
  Proof.
    move=> A dirA.
    split.
    - move=> //= u; apply: above_lub; auto.
      case; cbn.
      + move=> s.
        apply: ltT'.
        * apply: dlub_is_ub; left; apply: lub_intro; eauto.
        * done.
      + move=> _.
        apply: ltT'.
        * apply: dlub_is_ub.
          by right.
        * done.

    - move=> z zub.
      apply: lub_univ; auto.
      + case; cbn.
        * move=> h.
          suff: ∃ i, A i.
          -- move=> [i u].
             apply: ltT; last by apply: zub.
             apply: ltT'.
             ++ apply: lub_is_ub.
                apply: dlub_is_lub.
                by left.
             ++ done.
          -- apply: (lub_univ A).
             ++ by apply: dlub_is_lub.
             ++ apply: lub_is_ub.
                apply: Σ_exists_is_lub.
             ++ done.
        * move=> _.
          case: dirA => [[i _] h].
          apply: ltT; last by apply: zub.
          apply: ltT'.
          -- apply: dlub_is_ub; by right.
          -- done.
  Qed.


  Definition make_path : Path.
    unshelve esplit.
    - move=> ϕ.
      apply: dlub.
      apply: path_fam_directed.
      exact: ϕ.
    - apply: dlub_continuous.
  Defined.
End PathFromLt.


Definition HasPath x y := ∃ p : Path, ap p ⊥ = x /\ ap p ⊤ = y.
Infix "⟿" := HasPath (at level 10).

Lemma fwd : ∀ x y : D, x ≤ y → x ⟿ y.
Proof.
  move=> x y xy.
  exists (make_path x y xy).
  split; cbn.
  - apply: lub_unique; auto.
    split.
    + case; last by done.
      by rewrite Σ_bot_rw.
    + move=> z h.
      apply: ltT'.
      * by apply: h; right.
      * done.
  - apply: lub_unique; auto.
    split; first by case.
    move=> z h.
    apply: ltT'.
    * by apply: h; left; rewrite Σ_top_rw.
    * done.
Qed.

Lemma bwd : ∀ x y : D, x ⟿ y → x ≤ y.
  move=> x y [α [<- <-]].
  apply: continuous_to_monotone.
  apply: ap_cont.
  apply: bottom_is_bottom.
Qed.

Lemma characterization : ∀ x y, (x ≤ y) = (x ⟿ y).
  move=> x y.
  apply: propositional_extensionality; split.
  - apply: fwd.
  - apply: bwd.
Qed.
