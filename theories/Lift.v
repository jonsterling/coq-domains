Require Import Preamble Preorder Poset Dcpo Sierpinski.

Set Primitive Projections.

(* Using the partial map classifier, via de Jong and Escardo. *)
Record L (A : Type) :=
  {defd : Σ;
   run :> defd → A}.

Arguments defd [A] _.
Arguments run [A] _.

Lemma L_ext : ∀ A (m n : L A) (p : defd m ≤ defd n) (q : defd n ≤ defd m), (∀ x, m x = n (p x)) → m = n.
Proof.
  move=> A [dm rm] [dn rn] //= p q h.
  have Q: dm = dn by apply: propext.
  dependent destruction Q.
  rewrite (_ : rm = rn) //.
  apply: funext => z.
  by rewrite (h z) (_ : p z = z).
Qed.

Section Lift.
  Context (A : Type).

  Definition L_lt (m n : L A) : Prop :=
    defd m → m = n.

  Lemma L_ltR : ∀ m, L_lt m m.
  Proof. by []. Qed.

  Lemma L_ltT : ∀ m n o, L_lt m n → L_lt n o → L_lt m o.
  Proof.
    move=> m n o mn no x.
    by rewrite mn // no -?mn.
  Qed.

  HB.instance Definition L_preorder_axioms := PreorderOfType.Build (L A) L_lt L_ltR L_ltT.

  Lemma L_make_lt (m n : L A) : (∀ x : defd m, ∃ y : defd n, m x = n y) → m ≤ n.
  Proof.
    move=> H x.
    case: (H x) => y H'.
    apply: L_ext; try by move=> ?.
    move=> p z.
    by rewrite (_ : p z = y) // (_ : z = x).
  Qed.


  Lemma L_ltE (m n : L A) : m ≤ n → n ≤ m → m = n.
  Proof.
    move=> mn nm.
    apply: L_ext.
    - by move=> ?; rewrite -mn.
    - by move=> ?; rewrite -nm.
    - move=> p x.
      specialize (mn x).
      dependent destruction mn.
      by rewrite (_ : p x = x).
  Qed.

  HB.instance Definition L_poset_axioms := PosetOfPreorder.Build (L A) L_ltE.

  Section Lub.
    Context (F : Family (L A)) (dirF : is_directed F).

    Lemma directed_defd_fam : is_directed (push_fam (λ x : L A, defd x) F).
    Proof.
      split.
      - by case: (nonempty _ dirF).
      - move=> //= i j.
        case: (predirected _ dirF i j) => k [ik jk].
        exists k; split; move=>?.
        + by rewrite -ik.
        + by rewrite -jk.
    Qed.


    Definition candidate_dlub : dlub (push_fam (λ x : L A, defd x) F) directed_defd_fam → A.
    Proof.
      move=> Q; apply: (iota (λ a, ∀ i x, F i x = a)); move: Q.
      apply: Σ_lub_elim=>//.
      move=> /= i x.
      exists (F i x); split=>//.
      move=> j; move: x.
      case: (predirected _ dirF i j) => k [ik jk] x y.
      generalize y x.
      rewrite (ik x) (jk y).
      by move=> a b; rewrite (_ : a = b).
    Defined.

    Definition candidate_dlub_compute : ∀ Q i x, F i x = candidate_dlub Q.
    Proof. by move=> Q i x; apply: (iota_prop (λ a, ∀ i x, F i x = a)). Qed.

    Opaque candidate_dlub.

    Definition L_dlub : L A.
    Proof.
      unshelve esplit.
      - by apply: dlub directed_defd_fam.
      - by apply: candidate_dlub.
    Defined.

    Lemma L_dlub_is_lub : is_lub F L_dlub.
    Proof.
      split.
      - move=> i.
        apply: L_make_lt =>/= x.
        unshelve esplit.
        + apply: Σ_lub_intro=>//.
          by exact: x.
        + by rewrite -(candidate_dlub_compute _ i x).
      - move=> m H; move=> //= x.
        apply: L_ext=>//.
        + apply: above_lub=>//=.
          move=> i; move=> z.
          by rewrite -(H i z).
        + move=> /= H' H''.
          rewrite (_ : H'' = x) //; move: H''.
          apply: Σ_lub_elim=>//= i z.
          rewrite -(candidate_dlub_compute x i).
          generalize z.
          by rewrite (H i z)=> ?; f_equal.
    Qed.

    Lemma L_ltHasDLub : ∃ m : L A, is_lub F m.
    Proof. exists L_dlub; by apply: L_dlub_is_lub. Qed.

    Lemma L_dlub_rw : ∀ m : L A, is_lub F m → m = L_dlub.
    Proof. move=> m ?; by apply/lub_unique/L_dlub_is_lub. Qed.
  End Lub.

  (* TODO: need to export more useful rewrite lemmas from here. Too much of what follows is depending on the concrete computation. *)

  HB.instance Definition L_dcpo_axioms := DcpoOfPoset.Build (L A) L_ltHasDLub.
End Lift.

Section Functor.

  Context {A B : Type} (f : A → B).

  Definition fmap : L A → L B.
  Proof. by move=> x; exists (defd x) => z; apply/f/x/z. Defined.

  Lemma fmap_cont : is_continuous fmap.
  Proof.
    move=> F dirF //= x xlub; split.
    - move=> //= i; move=> z.
      rewrite /fmap.
      rewrite (_ : F i = x); last by [].
      by apply: lub_is_ub xlub i z.

    - move=> //= y yub.
      rewrite (L_dlub_rw _ _ _ x xlub).
      apply: Σ_lub_elim; first by auto.
      move=> //= i di.
      rewrite -(yub i di) => //=.
      f_equal.
      apply: L_ext.
      + apply: above_lub; eauto.
        by move=> //= ?.
      + move=> ?.
        apply: Σ_lub_intro; eauto.
        by exact: di.
      + move=> //= Q/[dup].
        apply: Σ_lub_elim; first by auto.
        move=> //= j dj z.
        by rewrite candidate_dlub_compute.
  Qed.
End Functor.


Section Alg.
  Context (D : Dcppo.type).

  Definition alg_fam (x : L D) : Family D.
  Proof.
    exists (sum (defd x) True); case.
    + apply: x.
    + move=> _; exact: ⊥.
  Defined.

  Lemma alg_fam_dir (x : L D) : is_directed (alg_fam x).
  Proof.
    split.
    + by unshelve esplit; first by right.
    + case=> [z|[]]; case=> [z' | []];
      (unshelve esplit; first by (left + right)); split; try by [].
      by rewrite (_ : z = z').
  Qed.

  Definition alg : L D → D.
  Proof. by move=> x; apply/dlub/alg_fam_dir/x. Defined.

  Lemma alg_cont : is_continuous alg.
  Proof.
    move=> F dirF //= x xlub.
    rewrite /alg.
    split.
    - move=> //= i.
      apply: above_lub; first by auto.
      case; last by []; move=> di.
      rewrite -(lub_is_ub _ _ xlub i di).
      by apply: lub_is_ub.
    - move=> z zub; cbn.
      rewrite (L_dlub_rw _ _ _ x xlub).
      apply: above_lub; first by auto.
      case; last by [].
      move/[dup]; apply: Σ_lub_elim; auto.
      move=>//= i di u.
      rewrite -(candidate_dlub_compute _ F dirF u i di).
      apply: ltT'.
      + apply: zub i.
      + apply: ltT'.
        * apply: lub_is_ub; auto.
          by left.
        * by [].
  Qed.
End Alg.


Section UniversalProperty.

  Context (A : Type) (C : Dcppo.type) (f : A → C).

  Definition univ_map : L A → C := alg _ \o fmap f.

  Lemma univ_map_cont : is_continuous univ_map.
  Proof.
    apply: cmp_cont.
    - apply/cont_mono/fmap_cont.
    - apply: fmap_cont.
    - apply: alg_cont.
  Qed.

End UniversalProperty.
