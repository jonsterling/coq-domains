From Domains Require Import Preamble Preorder Poset Dcpo Sierpinski DcpoExponential.

Section Path.
  Context (D : Dcpo.type).

  Definition Path := map (HB.pack Σ) D.

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
        - by case=>a1; case=>a2 /=; (unshelve esplit; [left + right; assumption | eauto]).
      Qed.
    End Family.

    Lemma dlub_continuous : is_continuous (λ ϕ : Σ, dlub (path_fam ϕ) (path_fam_directed ϕ)).
    Proof.
      move=> A dirA p plub; split.
      - move=> //= u; apply: (above_lub _)=>//=; case.
        + move=>s; apply: ltT'.
          * by apply: dlub_is_ub; left; apply: (Σ_lub_intro A _ _ _ s).
          * by [].
        + move=> []; apply: ltT'.
          * by apply: dlub_is_ub; right.
          * by [].
      - move=> z zub; apply: (lub_univ _)=>//; case=>/=.
        + move=> h.
          suff: ∃ i, A i.
          * move=> [i u].
            apply: ltT; last by apply: zub.
            apply: ltT'.
            -- by apply: lub_is_ub; [apply: dlub_is_lub | left].
            -- by [].
          * apply: (lub_univ A); auto.
            -- by apply/lub_is_ub/Σ_exists_is_lub.
            -- suff: dlub A dirA = p by move=>->.
               by apply: lub_unique.
        + move=> _.
          case: dirA => [[i _] h].
          apply/ltT/zub; last by [].
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
    move=> ? ? [? [<- <-]].
    by apply/cont_mono/bottom_is_bottom/ap_cont.
  Qed.

  Lemma characterization : ∀ x y, (x ≤ y) = (x ⟿ y).
  Proof.
    move=> x y.
    by apply: propext; split; [apply: fwd | apply: bwd].
  Qed.

End Path.



Definition Σ_fun :=
  map (HB.pack Σ) (HB.pack Σ).

Definition Σ_line :=
  {ϕ : Σ & {ψ : Σ | ϕ ≤ ψ}}.

Notation "Σ^Σ" := Σ_fun.
Notation "Σ/=>" := Σ_line.

Definition phoa_fwd : Σ^Σ → Σ/=>.
Proof.
  move=> F.
  exists (ap F ⊥).
  exists (ap F ⊤).
  abstract by apply: cont_mono; first by apply: svalP.
Defined.

Definition phoa_bwd : Σ/=> → Σ^Σ.
Proof.
  move=> [ϕ [ψ h]].
  apply: make_path h.
Defined.

Ltac replace_goal H :=
  match goal with
  | [|- ?G] => rewrite (_ : G = H)
  end.

Definition phoa_bwd_fwd : ∀ F, phoa_bwd (phoa_fwd F) = F.
Proof.
  move=> F.
  apply: eq_sig=>//=.
  apply: funext=> ϕ.
  apply: propext; split.
  - apply: Σ_lub_elim=>//=.
    by case=>//= ?; apply: (cont_mono (ap F))=>//=; by apply: svalP.
  - move=> x.
    set fam := path_fam (HB.pack Σ) ⊥ ⊤ ϕ.
    set Ffam := path_fam (HB.pack Σ) (ap F ⊥) (ap F ⊤) ϕ.
    set dfam := path_fam_directed (HB.pack Σ) ⊥ ⊤ (top_is_top ⊥) ϕ.

    replace_goal (ap F (∃ i, fam i)).
    + apply: lub_unique; first by [].
      rewrite (_ : Ffam = push_fam (sval F) fam).
      * by congr Build_Family; apply: funext; case.
      * apply: (svalP F fam dfam).
        by apply: Σ_exists_is_lub.
    + rewrite /fam /dfam /Ffam.
      move: x.
      apply: (cont_mono (ap F)); first by apply: svalP.
      move=> u.
      exists (inl u).
      by rewrite //= Σ_top_rw.
Qed.

Definition phoa_fwd_bwd : ∀ x, phoa_fwd (phoa_bwd x) = x.
Proof.
  move=> [ϕ [ψ h]].
  rewrite /phoa_fwd //=.
  apply: eq_sigT=>//=.
  - set fam := path_fam (HB.pack Σ) ϕ ψ ⊥.
    set dfam := path_fam_directed (HB.pack Σ ) ϕ ψ h ⊥.
    apply: lub_unique=>//=.
    split.
    + case=>//=.
      by rewrite Σ_bot_rw.
    + move=>//= χ h'.
      apply: h' (inr _).
      done.
  - move=> H.
    apply: eq_sig=>//=.
    simplify_eqs.
    apply: lub_unique=>//=.
    split.
    + by case=>//=.
    + move=> //= χ h'.
      apply: h' (inl _).
      by rewrite Σ_top_rw.
Qed.
