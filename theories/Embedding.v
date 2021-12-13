From Domains Require Import Preamble Preorder Poset FilteredPoset Category Dcpo.

Section Embedding.
  Context {U A : Dcpo.type}.
  Context (e : U ~> A).

  Definition is_embedding : Prop := ∃ p : A ~> U, seq e p = idn _ ∧ ∀ x : A, sval e (sval p x) ≤ x.

End Embedding.

Lemma idn_is_embedding (A : Dcpo.type) : is_embedding (idn A).
Proof. by exists (idn _); split=>//; rewrite seqL. Qed.

Lemma seq_is_embedding (A B C : Dcpo.type) (f : A ~> B) (g : B ~> C) : is_embedding f → is_embedding g → is_embedding (seq f g).
Proof.
  move=> [pf [hf1 hf2]] [pg [hg1 hg2]].
  exists (seq pg pf); split.
  - by rewrite seqA -[seq g _]seqA hg1 seqL hf1.
  - move=> c.
    rewrite /seq//=.
    apply: ltT.
    + apply: (cont_mono (sval g) (svalP g)).
      apply: hf2.
    + apply: hg2.
Qed.

Definition embedding (A B : Dcpo.type) := {f : A ~> B | is_embedding f}.

Fact embedding_is_embedding {A B : Dcpo.type} (f : embedding A B) : is_embedding (sval f).
Proof. move: f; apply: svalP. Qed.

Hint Extern 0 => apply: embedding_is_embedding.


Record EP := EnEP {outep : Dcpo.type}.

Definition EP_hom (A B : EP) := embedding (outep A) (outep B).
Notation "EP.hom" := EP_hom.

HB.instance Definition _ := IsGraph.Build EP EP_hom.

Definition EP_idn (A : EP) : A ~> A.
Proof.
  rewrite /hom//=/EP.hom.
  exists (idn _).
  by apply: idn_is_embedding.
Defined.

Definition EP_seq (A B C : EP) : A ~> B → B ~> C → A ~> C.
Proof.
  rewrite /hom//=/EP.hom.
  move=> f g.
  unshelve esplit.
  - move: f g=>/sval+/sval+.
    by apply: seq.
  - by apply: seq_is_embedding.
Defined.

HB.instance Definition _ := IsPrecategory.Build EP EP_idn EP_seq.

Fact EP_seqL : has_seqL EP _ idn seq.
Proof. by move=> A B f; apply: eq_sig=>//; apply: seqL. Qed.

Fact EP_seqR : has_seqR EP _ idn seq.
Proof. by move=> A B f; apply: eq_sig=>//; apply: seqR. Qed.

Fact EP_seqA : has_seqA EP _ seq.
Proof. by move=> A B C D f g h; apply: eq_sig=>//=; apply: seqA. Qed.

HB.instance Definition _ := IsCategory.Build EP EP_seqL EP_seqR EP_seqA.

Context (I : FilteredPoset.type).

Definition Diagram := Functor.type (HB.pack (ToCat I)) (HB.pack EP).

Context (A : Diagram).

Definition bilim_carrier : Type :=
  ∀ i : ToCat I, outep (A i).

Definition bilim_carrier_ok (a : bilim_carrier) : Prop :=
  ∀ i j (ij : i ~> j), a j = sval (sval (fmap A ij)) (a i).

Definition bilim : Type :=
  {a : bilim_carrier | bilim_carrier_ok a}.

Definition bilim_lt (a b : bilim) : Prop :=
  ∀ i, (sval a i) ≤ sval b i.

Fact bilim_ltR (a : bilim) : bilim_lt a a.
Proof. by []. Qed.

Fact bilim_ltT (a b c : bilim) : bilim_lt a b → bilim_lt b c → bilim_lt a c.
Proof.
  move=> ab bc i.
  apply: ltT.
  - apply: ab.
  - apply: bc.
Qed.

HB.instance Definition _ := IsPreorder.Build bilim bilim_lt bilim_ltR bilim_ltT.

Fact bilim_ltE (a b : bilim) : a ≤ b → b ≤ a → a = b.
Proof.
  move=> ab ba.
  apply: eq_sig=>//.
  apply: depfunext=> i.
  apply: ltE.
  - apply: ab.
  - apply: ba.
Qed.

HB.instance Definition _ := PosetOfPreorder.Build bilim bilim_ltE.

Definition proj (i : _) : bilim → outep (A i).
Proof. by move/sval. Defined.


Fact proj_mono : ∀ i, is_monotone (proj i).
Proof. by move=> //= i a b; apply. Qed .

Definition bilim_dlub_carrier (F : Family bilim) (dirF : is_directed F) : bilim_carrier.
Proof.
  move=> i.
  apply: (dlub (push_fam (proj i) F)).
  abstract by apply/mono_preserves_dir/dirF/proj_mono.
Defined.

Lemma bilim_dlub_carrier_ok (F : Family bilim) (dirF : is_directed F) : bilim_carrier_ok (bilim_dlub_carrier F dirF).
Proof.
  move=> i j ij //=.
  rewrite /bilim_dlub_carrier.
  rewrite (_ : (sval (sval (fmap A ij)) (dlub (push_fam (proj i) F) _)) = dlub (push_fam (sval (sval (fmap A ij)) \o proj i) F) _).
  - move=> H.
    move: (mono_preserves_dir (proj_mono j) dirF) => H'.
    move: H H'.
    rewrite (_ : push_fam (sval (sval (fmap A ij)) \o proj i) = push_fam (proj j)).
    + congr push_fam.
      apply: funext=> a.
      move: (svalP a); rewrite /bilim_carrier_ok//=.
      by move=> <-.
    + move=> H H'.
      by congr dlub.
  - move=> H.
    apply: lub_unique=>//.
    apply: (svalP (sval (fmap A ij)) (push_fam (proj i) F) _ (dlub (push_fam (proj i) F) _))=>//=.
    by apply/mono_preserves_dir/dirF/proj_mono.
  - apply/mono_preserves_dir/dirF.
    move=> u v uv.
    rewrite /comp.
    apply/cont_mono/proj_mono/uv.
    apply: svalP.
Qed.

Definition bilim_dlub (F : Family bilim) (dirF : is_directed F) : bilim.
Proof. by exists (bilim_dlub_carrier F dirF); apply: bilim_dlub_carrier_ok. Defined.


Lemma bilim_dlub_is_ub (F : Family bilim) (dirF : is_directed F) : is_ub F (bilim_dlub F dirF).
Proof.
  move=> u i.
  rewrite /bilim_dlub/bilim_dlub_carrier//=.
  by apply: (lub_is_ub (push_fam (proj i) F)).
Qed.

Lemma bilim_dlub_univ (F : Family bilim) (dirF : is_directed F) : ∀ a : bilim, is_ub F a → bilim_dlub F dirF ≤ a.
Proof.
  move=> a uba i.
  rewrite /bilim_dlub/bilim_dlub_carrier//=.
  apply: lub_univ=>//=.
  move=> u.
  apply: uba.
Qed.

Fact bilim_has_dlub : ∀ (A : Family bilim), is_directed A → ∃ x, is_lub A x.
Proof.
  move=> F dirF//=.
  exists (bilim_dlub F dirF); split.
  - by apply: bilim_dlub_is_ub.
  - by apply: bilim_dlub_univ.
Qed.

HB.instance Definition _ := DcpoOfPoset.Build bilim bilim_has_dlub.
