Require Import Preamble Preorder Poset Dcpo.

(** It is sometimes useful to be able to treat the underlying order relation of a dcpo as a dcpo. *)

Section OrderSpace.
  Context (D : Dcpo.type).
  Definition Rel := { p : D * D | p.1 ≤ p.2}.

  Definition pi (p : Rel) : D * D := proj1_sig p.
  Definition pi1 (p : Rel) : D := (pi p).1.
  Definition pi2 (p : Rel) : D := (pi p).2.
  Definition rel (p : Rel) : pi1 p ≤ pi2 p := proj2_sig p.

  Definition Rel_lt (p q : Rel) : Prop :=
    pi1 p ≤ pi1 q
    ∧ pi2 p ≤ pi2 q.

  Lemma Rel_ltR : ∀ p : Rel, Rel_lt p p.
  Proof. by move=>?. Qed.

  Lemma Rel_ltT : ∀ p q r : Rel, Rel_lt p q → Rel_lt q r → Rel_lt p r.
  Proof. by move=> p q r [pq1 pq2] [qr1 qr2]; split; [apply/ltT/qr1 | apply/ltT/qr2]. Qed.

  HB.instance Definition Rel_preorder_axioms := PreorderOfType.Build Rel Rel_lt Rel_ltR Rel_ltT.

  Lemma Rel_ltE : ∀ p q : Rel, Rel_lt p q → Rel_lt q p → p = q.
  Proof.
    move=> [[p1 p2] ?] [[q1 q2] ?].
    rewrite /Rel_lt /pi1 /pi2 /=.
    move=> [pq1 pq2] [qp1 qp2].
    apply: eq_sig=>//=.
    by rewrite pair_equal_spec; split; apply: ltE.
  Qed.

  HB.instance Definition Rel_poset_axioms := PosetOfPreorder.Build Rel Rel_ltE.

  Section DLub.
    Context (A : Family Rel) (dirA : is_directed A).

    Definition Rel_dlub : Rel.
      unshelve esplit.
      - split.
        + unshelve apply: dlub.
          * by apply: push_fam A; apply: pi1.
          * split.
            -- by case: (nonempty A dirA) => i _; exists i.
            -- move=>i j; case: (predirected A dirA i j)=> k [[p1 p2] [q1 q2]].
               by exists k.
        + unshelve apply: dlub.
          * by apply: push_fam A; apply: pi2.
          * split.
            -- by case (nonempty A dirA) => i _; exists i.
            -- move=> i j; case (predirected A dirA i j)=> k [[p1 p2] [q1 q2]].
               by exists k.
      - apply: (above_lub (push_fam _ _))=>//= z.
        apply: ltT'.
        + by apply/dlub_is_ub/z.
        + by apply: rel.
    Defined.

    Lemma Rel_dlub_is_dlub : is_lub A Rel_dlub.
    Proof.
      split.
      - move=> i; split;
        by apply: ltT'; [apply dlub_is_lub | apply: ltR].
      - move=> //= [[p1 p2] pr] h; split; rewrite /pi1 /pi2 /=;
        by apply: (lub_univ _)=>// u; case: (h u).
    Qed.

    Lemma Rel_ltHasDLubs : ∃ x, is_lub A x.
    Proof. by exists Rel_dlub; apply: Rel_dlub_is_dlub. Qed.
  End DLub.

  HB.instance Definition Rel_dcpo_axioms := DcpoOfPoset.Build Rel Rel_ltHasDLubs.

End OrderSpace.
