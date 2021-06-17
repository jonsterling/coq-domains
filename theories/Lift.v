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

    Definition candidate_dlub_compute : ∀ Q, ∀ i x, F i x = candidate_dlub Q.
    Proof. by move=> Q i x; apply: (iota_prop (λ a, ∀ i x, F i x = a)). Qed.

    Opaque candidate_dlub.

    Lemma L_ltHasDLub : ∃ m : L A, is_lub F m.
    Proof.
      unshelve esplit.
      - unshelve esplit.
        + by apply: dlub directed_defd_fam.
        + by apply: candidate_dlub.
      - split.
        + move=> i.
          apply: L_make_lt =>/= x.
          unshelve esplit.
          * apply: Σ_lub_intro=>//.
            by exact: x.
          * by rewrite -(candidate_dlub_compute _ i x).
        + move=> m H; move=> //= x.
          apply: L_ext=>//.
          * apply: above_lub=>//=.
            move=> i; move=> z.
            by rewrite -(H i z).
          * move=> /= H' H''.
            rewrite (_ : H'' = x) //; move: H''.
            apply: Σ_lub_elim=>//= i z.
            rewrite -(candidate_dlub_compute x i).
            generalize z.
            by rewrite (H i z)=> ?; f_equal.
    Qed.
  End Lub.

  HB.instance Definition L_dpco_axioms := DcpoOfPoset.Build (L A) L_ltHasDLub.
End Lift.
