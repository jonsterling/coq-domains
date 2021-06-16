Require Import Preamble Preorder Poset Dcpo Sierpinski.
Require Import Program.Equality.

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
  have Q: dm = dn; first by [apply: propositional_extensionality; split; auto].
  dependent destruction Q.
  have Q: rm = rn.
  - apply: functional_extensionality => z.
    specialize (h z).
    replace (p z) with z in h; first by auto.
    apply: proof_irrelevance.
  - by rewrite Q.
Qed.

Section Lift.
  Context (A : Type).

  Definition L_lt (m n : L A) : Prop :=
    defd m → m = n.

  Lemma L_ltR : ∀ m, L_lt m m.
  Proof. by compute. Qed.

  Lemma L_ltT : ∀ m n o, L_lt m n → L_lt n o → L_lt m o.
  Proof.
    move=> m n o; compute; move=> mn no x.
    rewrite mn; first by auto.
    by rewrite no -?mn.
  Qed.

  HB.instance Definition L_preorder_axioms := PreorderOfType.Build (L A) L_lt L_ltR L_ltT.

  Lemma L_make_lt (m n : L A) : (∀ x : defd m, ∃ y : defd n, m x = n y) → m ≤ n.
  Proof.
    move=> H x.
    case: (H x) => y H'.
    apply: L_ext.
    - by move=> ?.
    - by move=> ?.
    - move=> p z.
      replace (p z) with y; last by apply: proof_irrelevance.
      replace z with x; last by apply: proof_irrelevance.
      exact: H'.
  Qed.


  Lemma L_ltE (m n : L A) : m ≤ n → n ≤ m → m = n.
  Proof.
    move=> mn nm.
    apply: L_ext.
    - move=> ?; by rewrite <- mn.
    - move=> ?; by rewrite <- nm.
    - move=> p x.
      specialize (mn x).
      dependent destruction mn.
      by replace (p x) with x; last by apply: proof_irrelevance.
  Qed.

  HB.instance Definition L_poset_axioms := PosetOfPreorder.Build (L A) L_ltE.

  Section Lub.
    Context (F : Family (L A)) (dirF : is_directed F).

    Lemma directed_defd_fam : is_directed (push_fam (λ x : L A, defd x) F).
    Proof.
      split.
      - case: (nonempty _ dirF); by cbn.
      - move=> //= i j.
        case: (predirected _ dirF i j) => k [ik jk].
        exists k; split.
        + move=> ?; by rewrite -ik.
        + move=> ?; by rewrite -jk.
    Qed.


   Definition candidate_dlub : dlub (push_fam (λ x : L A, defd x) F) directed_defd_fam → A.
   Proof.
     move=> Q.
     apply: (iota (λ a, ∀ i x, F i x = a)).
     rewrite <- (lub_unique _ _ _ (Σ_exists_is_lub _) (dlub_is_lub _ _)) in Q.
     case: Q => //= i x.
     exists (F i x); split.
     - move=> j; move: x.
       case: (predirected _ dirF i j) => k [ik jk] x y.
       specialize (jk y).
       specialize (ik x).
       generalize y x.
       rewrite ik jk.
       move=> ? ?; f_equal; apply: proof_irrelevance.
     - done.
   Defined.

   Definition candidate_dlub_compute : ∀ Q, ∀ i x, F i x = candidate_dlub Q.
   Proof. move=> Q i x; apply: (iota_prop (λ a, ∀ i x, F i x = a)). Qed.

   (** This proof is totally horrible. *)
   Lemma L_ltHasDLub : ∃ m : L A, is_lub F m.
   Proof.
     unshelve esplit.
     - unshelve esplit.
       + apply: dlub directed_defd_fam.
       + apply: candidate_dlub.
     - split.
       + move=> i.
         apply: L_make_lt; cbn.
         move=> x.
         unshelve esplit.
         * apply: lub_intro.
           -- apply: dlub_is_lub.
           -- exact: x.
         * by rewrite -(candidate_dlub_compute _ i x).
       + move=> m H.
         move=> //= x.
         apply: L_ext.
         * apply: above_lub; first by apply: dlub_is_lub.
           move=> //= i; move=> z.
           specialize (H i z).
           by rewrite H in z.
         * done.
         * move=> //= H' H''.
           rewrite /ssr_suff.
           replace H'' with x; last by apply: proof_irrelevance.
           rewrite <- (lub_unique _ _ _ (Σ_exists_is_lub _) (dlub_is_lub _ _)) in H''.
           case: H'' => //= i z.
           rewrite -(candidate_dlub_compute x i).
           specialize (H i z).
           generalize z.
           rewrite H.
           move=> ?.
           f_equal.
           apply: proof_irrelevance.
   Qed.
  End Lub.

  HB.instance Definition L_dpco_axioms := DcpoOfPoset.Build (L A) L_ltHasDLub.

End Lift.
