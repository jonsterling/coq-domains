Require Import Preamble Preorder Poset Dcpo UNat.

Set Primitive Projections.

(** An "intensional" lift operation that can track termination in a (potentially infinite) number of steps. *)
Record IL (A : Type) :=
  {beh : UNat;
   run :> UNat_defd beh → A}.

Arguments beh [A] _.
Arguments run [A] _.

Lemma IL_ext : ∀ A (m n : IL A) (p : beh m ≤ beh n) (q : beh n ≤ beh m), (∀ x y, m x = n y) → m = n.
Proof.
  move=> A [bm rm] [bn rn] //= p q h.
  have Q: bm = bn by apply: ltE.
  dependent destruction Q.
  rewrite (_ : rm = rn) //.
  apply: funext=> z.
  by rewrite (h z z).
Qed.

Section Lift.
  Context (A : Type).

  Definition IL_lt (m n : IL A) : Prop :=
    beh m ≤ beh n ∧ ∀ u v, m u = n v.

  Lemma IL_ltR : ∀ m, IL_lt m m.
  Proof.
    move=> m; split; first by [].
    move=> u v.
    by rewrite (_ : u = v).
  Qed.

  Lemma IL_ltT : ∀ m n o, IL_lt m n → IL_lt n o → IL_lt m o.
  Proof.
    move=> m n o [mn0 mn1] [no0 n1].
    split.
    - apply: ltT mn0 no0.
    - move=> u v.
      rewrite mn1; first by [].
      case: u=> k ?.
      by exists k; apply: mn0.
  Qed.

  HB.instance Definition IL_preorder_axioms := PreorderOfType.Build (IL A) IL_lt IL_ltR IL_ltT.

  Lemma IL_ltE (m n : IL A) : m ≤ n → n ≤ m → m = n.
  Proof. by move=> [mn0 mn1] [nm0 nm1]; apply: IL_ext. Qed.

  HB.instance Definition IL_poset_axioms := PosetOfPreorder.Build (IL A) IL_ltE.


  Section Lub.
    Context (F : Family (IL A)) (dirF : is_directed F).

    Lemma directed_defd_fam : is_directed (push_fam (λ x : IL A, beh x) F).
    Proof.
      split.
      - by case: (nonempty _ dirF).
      - move=> //= i j.
        case: (predirected _ dirF i j)=> k [[ik0 ik1] [jk0 jk1]].
        exists k; split; move=> ?.
        + apply: ik0.
        + apply: jk0.
    Qed.

    Definition candidate_dlub : UNat_defd (dlub (push_fam (λ x : IL A, beh x) F) directed_defd_fam) → A.
    Proof.
      move=> Q; apply: (iota (λ a, ∀ i x, F i x = a)); move: Q.
      case=> x.
      apply: UNat_lub_elim=>//.
      move=>/=i y u.
      unshelve esplit.
      - apply: F.
        by exists y; eauto.
      - split=>//.
        move=> j.
        case: (predirected _ dirF i j)=> k [[ik0 ik1] [jk0 jk1]] [z w].
        rewrite jk1//.
        by exists z; apply: jk0.
    Defined.

    Definition candidate_dlub_compute : ∀ Q i x, F i x = candidate_dlub Q.
    Proof. by move=> Q i x; apply: (iota_prop (λ a, ∀ i x, F i x = a)). Qed.

    Opaque candidate_dlub.

    Definition IL_dlub : IL A.
    Proof.
      unshelve esplit.
      - by apply: dlub directed_defd_fam.
      - by apply: candidate_dlub.
    Defined.

    Lemma IL_dlub_is_lub : is_lub F IL_dlub.
    Proof.
      split.
      - move=> i; split.
        + move=> x hx.
          apply: UNat_lub_intro=>//.
          by exact: hx.
        + by move=> u ?; rewrite /IL_dlub /= -(candidate_dlub_compute _ i u).
      - move=> m H; split.
        + move=> x.
          apply: UNat_lub_elim=>//i u.
          case: (H i)=> Hi0 Hi1.
          by apply: Hi0.
        + rewrite /IL_dlub //=.
          case; apply: UNat_lub_elim_dep=>//.
          move=> i k hk w [l hl].
          rewrite -(candidate_dlub_compute _ i (ex_intro _ _ hk)).
          case: (H i)=> Hi0 Hi1.
          apply: Hi1.
    Qed.

    Lemma IL_ltHasDLub : ∃ m : IL A, is_lub F m.
    Proof. by exists IL_dlub; apply: IL_dlub_is_lub. Qed.

    Lemma IL_dlub_rw : ∀ m : IL A, is_lub F m → m = IL_dlub.
    Proof. by move=> m ?; apply/lub_unique/IL_dlub_is_lub. Qed.
  End Lub.


  Definition IL_bot : IL A.
  Proof. exists ⊥; apply: UNat_bot_elim. Defined.

  Lemma IL_bot_is_bot : is_bottom IL_bot.
  Proof. by move=> ?; split=>//; apply: UNat_bot_elim. Qed.

  Lemma IL_has_bot : ∃ x : IL A, is_bottom x.
  Proof. by exists IL_bot; apply: IL_bot_is_bot. Qed.

  HB.instance Definition IL_dcpo_axioms := DcpoOfPoset.Build (IL A) IL_ltHasDLub.
  HB.instance Definition IL_pointed_poset_axioms := PointedPosetOfPoset.Build (IL A) IL_has_bot.
End Lift.
