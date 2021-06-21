From Domains Require Import Preamble Preorder Poset Dcpo.

Section Map.
  Context (D E : Dcpo.type).

  Definition map := {f : D → E | is_continuous f}.
  Definition ap (f : map) : D → E := proj1_sig f.
  Definition ap_cont (f : map) : is_continuous (ap f) := proj2_sig f.

  Lemma map_ext : ∀ f g, ap f = ap g → f = g.
  Proof. by rewrite /map => f g fg; apply: eq_sig. Qed.

  Definition map_lt (f g : map) : Prop :=
    ∀ x, ap f x ≤ ap g x.

  Lemma map_ltR : ∀ f, map_lt f f.
  Proof. by move=>?. Qed.

  Lemma map_ltT : ∀ f g h, map_lt f g → map_lt g h → map_lt f h.
  Proof.
    move=> f g h fg gh x.
    by apply: ltT; [apply: fg | apply: gh].
  Qed.

  HB.instance Definition map_preorder_axioms := PreorderOfType.Build map map_lt map_ltR map_ltT.

  Lemma map_ltE : ∀ f g : map, f ≤ g → g ≤ f → f = g.
  Proof.
    move=> f g fg gf.
    apply/map_ext/funext=>x.
    by apply: ltE; [apply: fg | apply: gf].
  Qed.

  HB.instance Definition map_poset_axioms := PosetOfPreorder.Build map map_ltE.

  Section Lub.

    Context (A : Family map).

    Lemma push_ap_directed : ∀ (x : D), is_directed A → is_directed (push_fam (λ f, ap f x) A).
    Proof.
      move=> x dir; split; first by apply: nonempty dir.
      move=> //= i j.
      case: (predirected A dir i j) => k [ij jk].
      by exists k; split; [apply: ij | apply: jk].
    Qed.

    Section Map.
      Context (dir : is_directed A).

      Definition dlub_fun : D → E :=
        λ x,
        dlub (push_fam (λ f, ap f x) A) (push_ap_directed x dir).

      Lemma dlub_fun_continuous : is_continuous dlub_fun.
      Proof.
        apply: preserves_dlub_cont.
        move=> F dirF; split.
        - move=> //= i.
          apply: above_lub; first by apply: dlub_is_lub.
          move=> //= z.
          apply: ltT.
          + by apply: cont_mono; [apply: ap_cont | apply: dlub_is_ub].
          + by apply: (dlub_is_ub (push_fam _ A)).
        - move=> z //= H.
          apply: dlub_least => //= x.
          apply: lub_univ; first by [apply: ap_cont; eauto].
          move=> //= y.
          apply: ltT'; first by apply: H.
          by apply: (dlub_is_ub (push_fam _ A)).
      Qed.

      Lemma map_ltHasDLubs : ∃ f, is_lub A f.
      Proof.
        unshelve esplit.
        - by exists dlub_fun; apply: dlub_fun_continuous.
        - split=>/=.
          + move=> i; move=> ?.
            by apply: (dlub_is_ub (push_fam _ _)).
          + move=> f Hf; move=> ?.
            apply: dlub_least => ?.
            by apply: Hf.
      Qed.
    End Map.
  End Lub.

  HB.instance Definition map_dcpo_axioms := DcpoOfPoset.Build map map_ltHasDLubs.

End Map.

Arguments ap [D] [E].
