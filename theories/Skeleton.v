From Domains Require Import Preamble Preorder Poset.

Section Skeleton.
  Variable A : Preorder.type.

  Local Definition rel (x y : A) : Prop :=
    x ≤ y ∧ y ≤ x.

  Instance : RelationClasses.Reflexive rel.
  Proof. by move=> x; split. Qed.

  Instance : RelationClasses.Symmetric rel.
  Proof. by move=> x y [xy yx]; split. Qed.

  Instance : RelationClasses.Transitive rel.
  Proof.
    move=> x y z [xy yx] [yz zy]; split.
    - by apply: ltT; eauto.
    - by apply: ltT; eauto.
  Qed.

  Instance : RelationClasses.Equivalence rel.
  Proof. by split; typeclasses eauto. Defined.

  Definition skel := Quotient.T A rel.
  Definition cls : A → skel := Quotient.intro.

  Definition skel_lt (u v : skel) : Prop :=
    ∀ x y, cls x = u → cls y = v → x ≤ y.

  Lemma skel_ltT : ∀ u v w : skel, skel_lt u v → skel_lt v w → skel_lt u w.
  Proof.
    apply: Quotient.indp=> x.
    apply: Quotient.indp=> y.
    apply: Quotient.indp=> z.
    move=> xy yz x' z' xx' zz'.
    apply: ltT.
    - by apply: xy.
    - by apply: yz.
  Qed.

  Lemma skel_ltR : ∀ u, skel_lt u u.
  Proof.
    apply: Quotient.indp=> x.
    move=> x' x''.
    move=>/Quotient.eff [x'x xx'].
    move=>/Quotient.eff [x''x xx''].
    by apply: ltT; eauto.
  Qed.

  HB.instance Definition _ := PreorderOfType.Build skel skel_lt skel_ltR skel_ltT.

  Lemma skel_ltE : ∀ u v : skel, u ≤ v → v ≤ u → u = v.
  Proof.
    apply: Quotient.indp=> x.
    apply: Quotient.indp=> y.
    move=> xy yx.
    apply: Quotient.glue; split.
    + by apply: xy.
    + by apply: yx.
  Qed.

  HB.instance Definition _ := PosetOfPreorder.Build skel skel_ltE.

  Lemma cls_mono : is_monotone cls.
  Proof.
    move=> x y xy x' y'.
    move=>/Quotient.eff [x'x xx'].
    move=>/Quotient.eff [y'y yy'].
    apply: ltT.
    - by apply: x'x.
    - apply: ltT.
      + by apply: xy.
      + by apply: yy'.
  Qed.

  Lemma cls_full : forall x y : A, cls x ≤ cls y → x ≤ y.
  Proof. by move=> x y; apply. Qed.

  Lemma cls_surj : surjective cls.
  Proof. by apply: Quotient.indp=> x; exists x. Qed.
End Skeleton.
