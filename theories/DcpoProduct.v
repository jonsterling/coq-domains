From Domains Require Import Preamble Preorder Poset Dcpo.

Section Product.
  Context (D E : Dcpo.type).

  Definition prod_lt (p q : prod D E) : Prop :=
    p.1 ≤ q.1 ∧ p.2 ≤ q.2.

  Lemma prod_ltR : ∀ p, prod_lt p p.
  Proof. by []. Qed.

  Lemma prod_ltT : ∀ p q r, prod_lt p q → prod_lt q r → prod_lt p r.
  Proof.
    by move=> [x1 y1][x2 y2][x3 y3][/= ? ?] [/= Hx Hy]; split=>/=;
    [apply/ltT/Hx | apply/ltT/Hy].
  Qed.

  HB.instance Definition prod_preorder_axioms := IsPreorder.Build (prod D E) prod_lt prod_ltR prod_ltT.

  Lemma prod_ltE : ∀ p q, prod_lt p q → prod_lt q p → p = q.
  Proof.
    move=> [? ?] [? ?] //= [/= h1 h2] [/= h'1 h'2].
    by rewrite (ltE _ _ h1 h'1) (ltE _ _ h2 h'2).
  Qed.

  HB.instance Definition prod_poset_axioms := PosetOfPreorder.Build (prod D E) prod_ltE.

  Section DLub.
    Context (A : Family (prod D E)) (dirA : is_directed A).

    Definition prod_dlub : prod D E.
    Proof.
      split.
      - unshelve apply: dlub.
        + by apply: push_fam A; apply: fst.
        + split.
          * by case (nonempty A dirA) => i _; exists i.
          * by move=> i j; case (predirected A dirA i j)=> k [[p1 p2] [q1 q2]]; exists k.
      - unshelve apply: dlub.
        + by apply: push_fam A; apply: snd.
        + split.
          * by case (nonempty A dirA) => i _; exists i.
          * by move=> i j; case (predirected A dirA i j)=> k [[p1 p2] [q1 q2]]; exists k.
    Defined.

    Lemma prod_dlub_is_lub : is_lub A prod_dlub.
    Proof.
      split.
      - move=> i; split;
        by apply: ltT'; [apply dlub_is_lub | apply: ltR].
      - move=> //= [p1 p2] h; split=>/=;
        by apply: (lub_univ _)=>// u; case: (h u).
    Qed.

    Lemma prod_ltHasDLubs : ∃ x, is_lub A x.
    Proof. by exists prod_dlub; apply: prod_dlub_is_lub. Qed.
  End DLub.

  HB.instance Definition prod_dcpo_axioms := DcpoOfPoset.Build (prod D E) prod_ltHasDLubs.

  Lemma fst_continous : is_continuous fst.
  Proof.
    move=>/= A dirA x xlub; split.
    - move=>/= i.
      suff: A i ≤ x by case.
      by apply: lub_is_ub.
    - move=>/= y yub.
      case: (lub_univ A x xlub (y,x.2))=>//.
      move=>/= i; split=>/=.
      + by apply: yub.
      + suff: A i ≤ x by case.
        by apply: lub_is_ub.
  Qed.

  Lemma snd_continous : is_continuous snd.
  Proof.
    move=>/= A dirA x xlub; split.
    - move=>/= i.
      suff: A i ≤ x by case.
      by apply: lub_is_ub.
    - move=>/= y yub.
      case: (lub_univ A x xlub (x.1,y))=>//.
      move=>/= i; split=>/=.
      * suff: A i ≤ x by case.
        by apply: lub_is_ub.
      * by apply: yub.
  Qed.

  Lemma pair_left_continous : ∀ x, is_continuous (pair x).
  Proof.
    move=> x; split.
    - move=>/= i; split=>//=.
      by apply: lub_is_ub.
    - move=>/= z zub.
      split=>/=.
      + case: (nonempty _ h) => i _.
        by case: (zub i).
      + apply: lub_univ; first by eauto.
        move=> i.
        suff: (z.1, A i) ≤ z by case.
        by case: (zub i).
  Qed.

  Lemma pair_right_continous : ∀ x, is_continuous (fun y => pair y x).
  Proof.
    move=> x; split.
    - move=>/= i; split=>//=.
      by apply: lub_is_ub.
    - move=>/= z zub.
      split=>/=.
      + apply: lub_univ; first by eauto.
        move=> i.
        suff: (A i, z.2) ≤ z by case.
        by case: (zub i).
      + case: (nonempty _ h) => i _.
        by case: (zub i).
  Qed.
End Product.
