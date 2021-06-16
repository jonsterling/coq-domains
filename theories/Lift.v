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

    (** TODO, not proved yet. *)
    Definition L_dlub : L A.
    Proof.
      unshelve esplit.
      - apply: dlub directed_defd_fam.
      - (* To do this, we need to be able to eliminate from an existential into a singleton --- the type will be a singleton ultimately because F is directed. *)
    Abort.

  End Lub.

End Lift.
