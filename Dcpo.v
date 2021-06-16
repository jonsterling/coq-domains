Require Import Preamble.
Require Import Preorder.
Require Import Poset.

HB.mixin Record DcpoOfPoset D of Poset D :=
  {ltHasDirLubs : ∀ (A : Family D), is_directed A → ∃ x, is_lub A x}.

HB.structure Definition Dcpo := {D of DcpoOfPoset D & Poset D}.
HB.structure Definition Dcppo := {D of Dcpo D & PointedPoset D}.

Section DLub.
  Context {D : Dcpo.type} (A : Family D) (dir : is_directed A).

  Definition dlub_bundled : {x : D | is_lub A x}.
  Proof.
    apply: constructive_definite_description.
    case: (ltHasDirLubs A dir) => //= x xlub.
    exists x; split; first by done.
    move=> y ylub.
    apply: lub_unique; by eauto.
  Qed.

  Definition dlub : D.
  Proof. case: dlub_bundled => x _; exact: x. Defined.

  Lemma dlub_is_lub : is_lub A dlub.
  Proof. rewrite /dlub; by case: dlub_bundled. Qed.

  Lemma dlub_is_ub : is_ub A dlub.
  Proof. rewrite /dlub; case: dlub_bundled => ? [? ?]; auto. Qed.

  Lemma dlub_least : ∀ z : D, is_ub A z → dlub ≤ z.
  Proof. rewrite /dlub; case: dlub_bundled => ? [? ?]; auto. Qed.

  Opaque dlub.
End DLub.

Definition push_fam {D E : Poset.type} (f : D → E) (F : Family D) : Family E.
Proof.
  exists (fam_ix F).
  move=> i.
  apply: f.
  exact: (F i).
Defined.

Definition is_continuous {D E : Dcpo.type} (f : D → E) :=
  ∀ (A : Family D) (h : is_directed A),
    is_lub (push_fam f A) (f (dlub A h)).

Definition leq_family {D : Dcpo.type} (x y : D) : Family D.
  exists bool; case.
  - exact: x.
  - exact: y.
Defined.

Lemma leq_family_directed {D : Dcpo.type} : ∀ x y : D, x ≤ y → is_directed (leq_family x y).
Proof. move=> *; split; repeat case; try (by [exists true] + by [exists false]). Qed.

Lemma leq_to_lub {D : Dcpo.type} : ∀ x y : D, ∀ p : x ≤ y, y = dlub (leq_family x y) (leq_family_directed x y p).
Proof.
  move=> x y xy.
  apply: (lub_unique (leq_family x y)); last by apply: dlub_is_lub.
  split.
  - case; [auto | apply: ltR].
  - move=> z hz.
    apply: hz false.
Qed.


Lemma continuous_to_monotone {D E : Dcpo.type} (f : D → E) : is_continuous f → ∀ x y, x ≤ y → f x ≤ f y.
Proof.
  move=> fcont x y p.
  rewrite (leq_to_lub x y p).
  case: (fcont (leq_family x y) (leq_family_directed x y p)) => ub _.
  apply: ub true.
Qed.


Module Σ.
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
End Σ.


Module Exponential.
  Context (D E : Dcpo.type).

  Definition map := {f : D → E | is_continuous f}.
  Definition ap (f : map) : D → E := proj1_sig f.
  Definition ap_cont (f : map) : is_continuous (ap f) := proj2_sig f.

  Lemma map_ext : ∀ f g, ap f = ap g → f = g.
  Proof.
    rewrite /map.
    move=> f g fg.
    apply: eq_sig.
    apply: proof_irrelevance.
  Qed.

  Definition map_lt (f g : map) : Prop :=
    ∀ x, ap f x ≤ ap g x.

  Lemma map_ltR : ∀ f, map_lt f f.
  Proof. move=> f x; apply: ltR. Qed.

  Lemma map_ltT : ∀ f g h, map_lt f g → map_lt g h → map_lt f h.
  Proof.
    move=> f g h fg gh x.
    apply: ltT.
    - apply: fg.
    - apply: gh.
  Qed.

  HB.instance Definition map_preorder_axioms := PreorderOfType.Build map map_lt map_ltR map_ltT.

  Lemma map_ltE : ∀ f g : map, f ≤ g → g ≤ f → f = g.
  Proof.
    move=> f g fg gf.
    apply: map_ext.
    extensionality x.
    apply: ltE.
    - apply: fg.
    - apply: gf.
  Qed.

  HB.instance Definition map_poset_axioms := PosetOfPreorder.Build map map_ltE.

  Section Lub.

    Context (A : Family map).

    Lemma push_ap_directed : ∀ (x : D), is_directed A → is_directed (push_fam (λ f, ap f x) A).
    Proof.
      move=> x dir.
      split.
      - apply: nonempty dir.
      - move=> //= i j.
        case: (predirected A dir i j) => k [ij jk].
        exists k; repeat split.
        + apply: ij.
        + apply: jk.
    Qed.

    Section Map.
      Context (dir : is_directed A).

      Definition dlub_fun : D → E :=
        λ x,
        dlub (push_fam (λ f, ap f x) A) (push_ap_directed x dir).

      Lemma dlub_fun_continuous : is_continuous dlub_fun.
      Proof.
        move=> F dirF; split.
        - move=> //= i.
          apply: above_lub.
          + apply: dlub_is_lub.
          + move=> //= z.
             apply: ltT.
             * apply: continuous_to_monotone.
                -- by apply: ap_cont.
                -- by apply: dlub_is_ub.
             * apply: (dlub_is_ub (push_fam _ A)).
        - move=> z //= H.
          apply: dlub_least.
          move=> //= x.
          apply: lub_univ.
          + apply: ap_cont.
          + move=> //= y.
            apply: ltT'.
            * by apply: H.
            * by apply: (dlub_is_ub (push_fam _ A) _).
      Qed.

      Lemma map_ltHasDLubs : ∃ f, is_lub A f.
      Proof.
        unshelve esplit.
        - unshelve esplit.
          + by apply: dlub_fun.
          + by apply: dlub_fun_continuous.
        - split; simpl.
          + move=> i; move=> ?.
            apply: (dlub_is_ub (push_fam _ A) _) i.
          + move=> f Hf; move=> ?.
            apply: dlub_least => ?.
            apply: Hf.
      Qed.
    End Map.
  End Lub.

  HB.instance Definition map_dcpo_axioms := DcpoOfPoset.Build map map_ltHasDLubs.
End Exponential.
