Require Import Preamble Preorder Poset Dcpo.

Section Product.
  Context (D E : Dcpo.type).

  Definition prod_lt (p q : prod D E) : Prop :=
    fst p ≤ fst q
    ∧ snd p ≤ snd q.

  Lemma prod_ltR : ∀ p, prod_lt p p.
  Proof. case; by split. Qed.

  Lemma prod_ltT : ∀ p q r, prod_lt p q → prod_lt q r → prod_lt p r.
  Proof. move=> [x1 y1] [x2 y2] [x3 y3] [? ?] [? ?]; split; apply: ltT; eauto. Qed.

  HB.instance Definition prod_preorder_axioms := PreorderOfType.Build (prod D E) prod_lt prod_ltR prod_ltT.

  Lemma prod_ltE : ∀ p q, prod_lt p q → prod_lt q p → p = q.
  Proof.
    move=> [? ?] [? ?] //= [//= h1 h2] [//= h'1 h'2].
    by rewrite (ltE _ _ h1 h'1) (ltE _ _ h2 h'2).
  Qed.

  HB.instance Definition prod_poset_axioms := PosetOfPreorder.Build (prod D E) prod_ltE.

  Section DLub.
    Context (A : Family (prod D E)) (dirA : is_directed A).

    Definition prod_dlub : prod D E.
    Proof.
      split.
      - unshelve apply: dlub.
        + apply: push_fam A; apply: fst.
        + split.
          * case (nonempty A dirA) => i _; by exists i.
          * move=> i j; case (predirected A dirA i j)=> k [[p1 p2] [q1 q2]]; exists k; by split.
      - unshelve apply: dlub.
        + apply: push_fam A; apply: snd.
        + split.
          * case (nonempty A dirA) => i _; by exists i.
          * move=> i j; case (predirected A dirA i j)=> k [[p1 p2] [q1 q2]]; exists k; by split.
    Defined.

    Lemma prod_dlub_is_lub : is_lub A prod_dlub.
    Proof.
      split.
      - move=> i; split.
        + apply: ltT'.
          * apply dlub_is_lub.
          * apply: ltR.
        + apply: ltT'.
          * apply dlub_is_lub.
          * apply: ltR.
      - move=> //= [p1 p2] h; split; cbn;
        (apply: lub_univ; first by auto);
        move=> //= u; by case: (h u).
    Qed.

    Lemma prod_ltHasDLubs : ∃ x, is_lub A x.
    Proof. exists prod_dlub; apply: prod_dlub_is_lub. Qed.
  End DLub.

  HB.instance Definition prod_dcpo_axioms := DcpoOfPoset.Build (prod D E) prod_ltHasDLubs.
End Product.
