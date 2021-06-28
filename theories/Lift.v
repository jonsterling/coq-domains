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
      move: {+}y {+}x.
      rewrite (ik x) (jk y) => ??.
      by congr (F _ _).
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
          by move: {+}z; rewrite (H i z) => ?; congr (m _).
    Qed.

    Lemma L_ltHasDLub : ∃ m : L A, is_lub F m.
    Proof. exists L_dlub; by apply: L_dlub_is_lub. Qed.

    Lemma L_dlub_rw : ∀ m : L A, is_lub F m → m = L_dlub.
    Proof. move=> m ?; by apply/lub_unique/L_dlub_is_lub. Qed.
  End Lub.

  Definition L_bot : L A.
  Proof. by exists False. Defined.

  Lemma L_bot_is_bot : is_bottom L_bot.
  Proof. by move=>?//=; case. Qed.

  Lemma L_has_bot : ∃ x : L A, is_bottom x.
  Proof. by exists L_bot; apply: L_bot_is_bot. Qed.

  HB.instance Definition L_dcpo_axioms := DcpoOfPoset.Build (L A) L_ltHasDLub.
  HB.instance Definition L_pointed_poset_axioms := PointedPosetOfPoset.Build (L A) L_has_bot.
End Lift.

Section Functor.

  Context {A B : Type} (f : A → B).

  Definition fmap : L A → L B.
  Proof. by move=> x; exists (defd x) => z; apply/f/x. Defined.

  Lemma fmap_cont : is_continuous fmap.
  Proof.
    move=>/= F dirF x xlub; split.
    - move=> /= i; move=> z.
      rewrite (_ : F i = x) //.
      by apply: lub_is_ub xlub i z.
    - move=> /= y yub.
      rewrite (L_dlub_rw _ _ _ x xlub).
      apply: Σ_lub_elim=>//= i di.
      rewrite -(yub i di) /=.
      congr (fmap _).
      apply: L_ext.
      + by apply: above_lub=>//= ?.
      + move=> ?.
        apply: Σ_lub_intro=>//.
        by exact: di.
      + move=> /= Q /[dup].
        apply: Σ_lub_elim=>//= j dj z.
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
    + by split=>//=; right.
    + case=> [z|[]]; case=> [z' | []];
      (unshelve esplit; first by (left + right)); split; try by [].
      by rewrite (_ : z = z').
  Qed.

  Definition alg : L D → D.
  Proof. by move=>x; apply/dlub/alg_fam_dir. Defined.

  Lemma alg_cont : is_continuous alg.
  Proof.
    move=>/= F dirF x xlub.
    rewrite /alg.
    split.
    - move=>/= i.
      apply: above_lub=>//.
      case=>// di.
      rewrite -(lub_is_ub _ _ xlub i di).
      by apply: lub_is_ub.
    - move=> z zub /=.
      rewrite (L_dlub_rw _ _ _ x xlub).
      apply: above_lub=>//.
      case=>// /[dup]; apply: Σ_lub_elim=>//= i di u.
      rewrite -(candidate_dlub_compute _ F dirF u i di).
      apply: ltT'.
      + apply: zub i.
      + apply: ltT'.
        * apply: lub_is_ub=>//.
          by left.
        * by [].
  Qed.
End Alg.


Section Unit.
  Context {A : Type}.
  Definition unit : A → L A.
  Proof. move=> a; exists ⊤ => _; exact: a. Defined.
End Unit.

Section Monad.

  Definition bind {A B} : (A -> L B) → L A -> L B.
  Proof.
    move=>f [d r].
    exists (∃ z : d, defd (f (r z)))=>y.
    apply: (f (r (ex_proj1 y))).
    by exact: ex_proj2 y.
  Defined.

  Definition flatten {A} : L (L A) -> L A := bind id.

End Monad.

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

  Lemma univ_map_strict : univ_map ⊥ = ⊥.
  Proof.
    rewrite /univ_map /alg /fmap /=.
    apply: lub_unique=>//.
    rewrite /alg_fam /=.
    split=>//.
    case=> [+ |[]]//=.
    rewrite (_ : ⊥ = L_bot _) //.
    by apply/bottom_is_unique/L_bot_is_bot.
  Qed.

  Lemma univ_map_compute : ∀ x, univ_map (unit x) = f x.
  Proof.
    move=> x.
    rewrite /univ_map /unit /fmap /alg /=.
    apply: lub_unique=>//.
    split; first by case.
    move=> c cub.
    apply: ltT'.
    - by apply: cub; left; rewrite Σ_top_rw.
    - by [].
  Qed.

  Definition is_univ_map (h : L A → C) := is_continuous h ∧ (h ⊥ = ⊥) ∧ ∀ x, h (unit x) = f x.

  (** In order to prove that there is at most one map satisfying
  [is_univ_map], we are going to use the continuity of candidate
  universal maps with respect to the following directed family. *)
  Section Fam.
    Context (x : L A).
    Local Definition fam : Family (L A).
    Proof.
      exists (sum (defd x) True); case.
      - by move=>?; apply/unit/x.
      - move=> _; exact: ⊥.
    Defined.

    Local Lemma fam_dir : is_directed fam.
    Proof.
      split.
      - by split=>//; right.
      - case=> [z|[]]; case=> [z'|[]]; (unshelve esplit; first by (left + right)); split=>//.
        by rewrite (_ : z = z').
    Qed.

    Local Lemma fam_lub : is_lub fam x.
    Proof.
      split.
      - case=> [z|[]] //=.
        apply: L_make_lt=> /= _.
        by exists z.
      - move=>/=y yub.
        apply: L_make_lt => z.
        have u : (⊤ : Σ) by rewrite Σ_top_rw.
        by rewrite -(yub (inl z) u) /=.
    Qed.
  End Fam.

  Lemma univ_map_unique : ∀ h h', is_univ_map h → is_univ_map h' → h = h'.
  Proof.
    move=> h h' [hcont [hstr hfac]] [h'cont [h'str h'fac]].
    apply: funext=>x.
    apply: lub_unique.
    - apply/hcont/fam_lub/fam_dir.
    - rewrite (_ : push_fam h (fam x) = push_fam h' (fam x)).
      + rewrite /push_fam; congr Build_Family.
        apply: funext; case=> [z|[]] /=.
        * by rewrite hfac h'fac.
        * by rewrite hstr h'str.
      + apply/h'cont/fam_lub/fam_dir.
  Qed.

  Lemma univ_map_is_univ_map : is_univ_map univ_map.
  Proof.
    split; [|split].
    - apply: univ_map_cont.
    - apply: univ_map_strict.
    - apply: univ_map_compute.
  Qed.

  Lemma universal_property : exists! f, is_univ_map f.
  Proof.
    exists univ_map.
    split.
    - apply: univ_map_is_univ_map.
    - by move=> ?; apply/univ_map_unique/univ_map_is_univ_map.
  Qed.
End UniversalProperty.
