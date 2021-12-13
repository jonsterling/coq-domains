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
  apply: funext=>?.
  by apply: h.
Qed.

Section Lift.
  Context (A : Type).

  Definition IL_lt (m n : IL A) : Prop :=
    beh m ≤ beh n ∧ ∀ u v, m u = n v.

  Lemma IL_ltR : ∀ m, IL_lt m m.
  Proof.
    move=> m; split=>// u v.
    by rewrite (_ : u = v).
  Qed.

  Lemma IL_ltT : ∀ m n o, IL_lt m n → IL_lt n o → IL_lt m o.
  Proof.
    move=> m n o [mn0 mn1] [no0 n1].
    split.
    - by apply: ltT mn0 no0.
    - move=> u v.
      rewrite mn1 //.
      case: u=> k ?.
      by exists k; apply: mn0.
  Qed.

  HB.instance Definition IL_preorder_axioms := IsPreorder.Build (IL A) IL_lt IL_ltR IL_ltT.

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
        by exists k; split; move=> ?; [apply: ik0 | apply: jk0].
    Qed.

    Definition candidate_dlub : UNat_defd (dlub (push_fam (λ x : IL A, beh x) F) directed_defd_fam) → A.
    Proof.
      move=> Q; apply: (iota (λ a, ∀ i x, F i x = a)); move: Q.
      case=> x.
      apply: UNat_lub_elim=>//= i y u.
      unshelve esplit.
      - apply: F.
        by exists y; apply: u.
      - split=>// j.
        case: (predirected _ dirF i j)=> k [[ik0 ik1] [jk0 jk1]] [z w].
        rewrite jk1 //.
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
          by apply: Hi1.
    Qed.

    Lemma IL_ltHasDLub : ∃ m : IL A, is_lub F m.
    Proof. by exists IL_dlub; apply: IL_dlub_is_lub. Qed.

    Lemma IL_dlub_rw : ∀ m : IL A, is_lub F m → m = IL_dlub.
    Proof. by move=> m ?; apply/lub_unique/IL_dlub_is_lub. Qed.
  End Lub.


  Definition IL_bot : IL A.
  Proof. by exists ⊥; apply: UNat_bot_elim. Defined.

  Lemma IL_bot_is_bot : is_bottom IL_bot.
  Proof. by move=> ?; split=>//; apply: UNat_bot_elim. Qed.

  Lemma IL_has_bot : ∃ x : IL A, is_bottom x.
  Proof. by exists IL_bot; apply: IL_bot_is_bot. Qed.

  HB.instance Definition IL_dcpo_axioms := DcpoOfPoset.Build (IL A) IL_ltHasDLub.
  HB.instance Definition IL_pointed_poset_axioms := PointedPosetOfPoset.Build (IL A) IL_has_bot.
End Lift.


Section Functor.
  Context {A B : Type} (f : A → B).

  Definition fmap : IL A → IL B.
  Proof. by move=> x; exists (beh x) => z; apply/f/x. Defined.

  Lemma fmap_cont : is_continuous fmap.
  Proof.
    move=>/= F dirF x xlub; split.
    - move=> /= i.
      case: (lub_is_ub _ _ xlub i)=> H0 H1.
      split=>//=??.
      by rewrite H1.
    - move=> /= y yub.
      rewrite (IL_dlub_rw _ _ _ x xlub).
      split.
      + move=> u.
        apply: UNat_lub_elim=>//= i k hk.
        by case: (yub i)=>X ?; apply: X.
      + case; apply: UNat_lub_elim_dep=>//= i ? h ? ?.
        case: (yub i) => _ /= <-.
        * move=> ?.
          rewrite candidate_dlub_compute.
          ** by move=> ?; congr (f (candidate_dlub _ _ _ _)).
          ** by esplit; apply: UNat_lub_intro; [apply: dlub_is_lub | exact: h].
        * by esplit; exact: h.
  Qed.
End Functor.

Section Unit.

  Context {A : Type}.

  Definition unit : A → IL A.
  Proof. by move=> a; exists ⊤=> ?; exact: a. Defined.

End Unit.

Section Monad.

  Definition bind {A B} : (A → IL B) → IL A → IL B.
  Proof.
    move=>f a.
    unshelve esplit.
    - apply: (UNat_dsum (beh a))=> k hk.
      apply/beh/f/a.
      by exists k.
    - move=>/= h.
      apply: (iota (λ b : B, ∀ u v, f (a u) v = b)).
      case: h=> u [v [w [hv [hw]]]] [vu wu].
      pose a' := a (ex_intro _ _ hv).
      pose b' := f a' (ex_intro _ _ hw).
      exists b'; split.
      + move=> [u' hu'] [v' hv'].
        rewrite /b' /a'.
        move: (ex_intro _ v' hv').
        move: (ex_intro _ w hw).
        move: (ex_intro _ v hv).
        move: (ex_intro _ u' hu').
        move=> h h'.
        rewrite (_ : h' = h) // => {h'} e e'.
        by rewrite (_ : e' = e).
      + move=> z hz.
        rewrite /b' /a'.
        by rewrite -(hz (ex_intro _ _ hv) (ex_intro _ _ hw)).
  Defined.

End Monad.
