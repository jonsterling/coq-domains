Require Import Preamble Preorder Poset Dcpo Sierpinski.

Set Primitive Projections.


Arguments proj1_sig {A P}.
Notation sval := proj1_sig.


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
  Context (A : Dcpo.type).

  Definition L_lt (m n : L A) : Prop :=
    ∀ z : defd m, ∃ z' : defd n, m z ≤ n z'.

  Lemma L_ltR : ∀ m, L_lt m m.
  Proof.
    move=> m zm.
    by exists zm.
  Qed.

  Lemma L_ltT : ∀ m n o, L_lt m n → L_lt n o → L_lt m o.
  Proof.
    move=> m n o mn no=> zm.
    case: (mn zm)=> zn mn'.
    case: (no zn)=> zo no'.
    exists zo.
    apply: ltT.
    - by apply: mn'.
    - by [].
  Qed.

  HB.instance Definition L_preorder_axioms := PreorderOfType.Build (L A) L_lt L_ltR L_ltT.

  Lemma L_ltE (m n : L A) : m ≤ n → n ≤ m → m = n.
  Proof.
    move=> mn nm.
    apply: L_ext.
    - move=> zm.
      by case: (mn zm).
    - move=> zn.
      by case: (nm zn).
    - move=> zmn zm.
      case: (mn zm)=>zn ?.
      case: (nm zn)=>zm'?.
      apply: ltE.
      + by rewrite (_ : zmn zm = zn)//=.
      + rewrite (_ : zmn zm = zn)//.
        by rewrite (_ : zm = zm').
  Qed.

  HB.instance Definition L_poset_axioms := PosetOfPreorder.Build (L A) L_ltE.

  Lemma L_lt_pi1 {m n : L A} : m ≤ n → defd m → defd n.
  Proof.
    move=> mn zm.
    by case: (mn zm).
  Qed.

  Lemma L_lt_pi2 {m n : L A} : m ≤ n → ∀ z z', m z ≤ n z'.
  Proof.
    move=> mn z z'.
    case: (mn z)=> zn.
    by rewrite (_ : zn = z').
  Qed.

  Section Lub.
    Context (F : Family (L A)) (dirF : is_directed F).

    Lemma directed_defd_fam : is_directed (push_fam (λ x : L A, defd x) F).
    Proof.
      split.
      - by case: (nonempty _ dirF).
      - move=> //= i j.
        case: (predirected _ dirF i j) => k [ik jk].
        exists k; split; move=>zFi.
        + by apply: (L_lt_pi1 ik).
        + by apply: (L_lt_pi1 jk).
    Qed.

    Section Candidate.
      Context (H : dlub (push_fam (λ x : L A, defd x) F) directed_defd_fam).

      Definition candidate_dlub_fam : Family A.
      Proof.
        unshelve esplit.
        - exact: ({i : fam_ix F | defd (F i)}).
        - move=> i.
          exact: F (sval i) (svalP i).
      Defined.

      Lemma candidate_dlub_fam_directed : is_directed candidate_dlub_fam.
      Proof.
        split.
        - move: H.
          apply: Σ_lub_elim=>//= i z.
          unshelve esplit=>//.
          by exists i.
        - move=> i j.
          case: (predirected _ dirF (sval i) (sval j))=> k [ik jk].
          unshelve esplit.
          + by exists k; case: (ik (svalP i)).
          + by split=>//=; apply: L_lt_pi2.
      Qed.

      Definition candidate_dlub : A.
      Proof. by apply: dlub candidate_dlub_fam_directed. Defined.

    End Candidate.

    Definition L_dlub : L A.
    Proof.
      unshelve esplit.
      - by apply: dlub directed_defd_fam.
      - by apply: candidate_dlub.
    Defined.

    Lemma L_dlub_is_lub : is_lub F L_dlub.
    Proof.
      split.
      - move=> i zi.
        unshelve esplit.
        + apply: Σ_lub_intro=>//.
          by exact: zi.
        + rewrite /L_dlub//=.
          rewrite /candidate_dlub//=.
          apply: ltT'.
          apply: lub_is_ub=>//.
          * by exists i.
          * rewrite /candidate_dlub_fam//=.
            by rewrite (_ :  (svalP (exist (λ i0 : fam_ix F, defd (F i0)) i zi)) = zi)//=.
      - move=>//= x xub.
        move/[dup]; apply: Σ_lub_elim=>//.
        move=> //= i zi z'.
        case: (xub i zi)=> zx h.
        exists zx.
        apply: lub_univ=>//=.
        move=> j.
        rewrite /candidate_dlub_fam//=.
        case: (xub (sval j) (svalP j))=> zx' h'.
        by rewrite (_ : zx = zx')//=.
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

  Context {A B : Dcpo.type} (f : A → B) (fcont : is_continuous f).

  Definition fmap : L A → L B.
  Proof. by move=> x; exists (defd x) => z; apply/f/x. Defined.

  Lemma fmap_cont : is_continuous fmap.
  Proof.
    move=>/= F dirF x xlub; split.
    - move=> /= i; move=> zi.
      case: (lub_is_ub _ _ xlub i zi)=> zx h.
      exists zx.
      rewrite /fmap//=.
      by apply: cont_mono=>//.
    - move=> /= y yub.
      rewrite (L_dlub_rw _ _ _ x xlub).
      move/[dup]; apply: Σ_lub_elim=>//.
      move=> //= i zi z'.
      case: (yub i zi)=> zy h.
      exists zy.
      apply: lub_univ.
      + apply: fcont=>//.
        by apply: candidate_dlub_fam_directed.
      + move=> //= j.
        case: (yub (sval j) (svalP j))=> zy' h'.
        by rewrite (_ : zy = zy').
  Qed.

  (* TODO: fmap strict *)
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
      case=>// di//=.
      case: (lub_is_ub _ _ xlub i di)=> zx h.
      apply: ltT.
      + by apply: h.
      + by apply: (lub_is_ub (alg_fam x) (dlub (alg_fam x) (alg_fam_dir x)) _ (inl zx)).

    - move=> z zub /=.
      rewrite (L_dlub_rw _ _ _ x xlub).
      apply: above_lub=>//.
      case=>// /[dup]; apply: Σ_lub_elim=>//= i di u.
      rewrite /candidate_dlub.
      apply: lub_univ=>//.
      move=> //= j.
      apply: ltT'.
      + by apply: zub (sval j).
      + simpl.
        apply: ltT'.
        * apply: lub_is_ub=>//=.
          left.
          apply: svalP j.
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

  Lemma bind_monotone {A B} (f : A -> L B) : is_monotone (bind f).
  Proof.
    move=>/= x y H; move=>/=H0.
    rewrite (_ : x = y) //.
    by apply/H/(ex_proj1 H0).
  Qed.

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
