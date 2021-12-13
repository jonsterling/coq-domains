From Domains Require Import Preamble Category.

HB.mixin Record IsPrefunctor (𝒞 𝒟 : Category.type) (F : 𝒞 → 𝒟) :=
  {fmap : ∀ x y : 𝒞, x ~> y → (F x) ~> (F y)}.

Section Properties.
  Context {𝒞 𝒟 : Category.type} (F : 𝒞 → 𝒟) (fmap : ∀ x y : 𝒞, x ~> y → (F x) ~> (F y)).

  Definition has_fmap_id := ∀ x : 𝒞, fmap _ _ (idn x) = idn (F x).
  Definition has_fmap_seq := ∀ (x y z : 𝒞) (f : x ~> y) (g : y ~> z), fmap _ _ (seq f g) = seq (fmap _ _ f) (fmap _ _ g).
End Properties.

HB.structure Definition Prefunctor 𝒞 𝒟 := {F of IsPrefunctor 𝒞 𝒟 F}.


HB.mixin Record IsFunctor (𝒞 𝒟 : Category.type) (F : 𝒞 → 𝒟) of IsPrefunctor 𝒞 𝒟 F :=
  {fmap_id : has_fmap_id F fmap;
   fmap_seq : has_fmap_seq F fmap}.

HB.structure Definition Functor 𝒞 𝒟 := {F of IsFunctor 𝒞 𝒟 F & IsPrefunctor 𝒞 𝒟 F}.

Arguments fmap {𝒞 𝒟} F [x] [y] f : rename.



Section Natural.
  Context {𝒞 𝒟 : Category.type} (F G : Functor.type 𝒞 𝒟).
  Definition Functor_prehom := ∀ x : 𝒞, F x ~> G x.
  Definition is_natural (f : Functor_prehom) :=
    ∀ (x y : 𝒞) (xy : x ~> y), seq (f x) (fmap G xy) = seq (fmap F xy) (f y).

  Definition Functor_hom := {f : Functor_prehom | is_natural f}.
End Natural.

Notation "Functor.hom" := Functor_hom.
Notation "Functor.prehom" := Functor_prehom.

HB.instance Definition _ 𝒞 𝒟 := IsGraph.Build (Functor.type 𝒞 𝒟) Functor.hom.

Section FunctorCategory.
  Context {𝒞 𝒟 : Category.type}.

  Definition Functor_idn (F : Functor.type 𝒞 𝒟) : F ~> F.
  Proof.
    unshelve esplit.
    - by move=> x; apply: idn.
    - abstract by move=> x y xy; rewrite seqL seqR.
  Defined.

  Definition Functor_seq (F G H : Functor.type 𝒞 𝒟) (f : F ~> G) (g : G ~> H) : F ~> H.
  Proof.
    unshelve esplit.
    - move=> x.
      exact: (seq (sval f x) (sval g x)).
    - abstract by move=> x y xy; rewrite seqA (svalP g x y xy) -seqA (svalP f x y xy) seqA.
  Defined.

  HB.instance Definition _ := IsPrecategory.Build (Functor.type 𝒞 𝒟) Functor_idn Functor_seq.

  Fact Functor_seqL : has_seqL (Functor.type 𝒞 𝒟) _ Functor_idn Functor_seq.
  Proof. by move=> F G f; apply: eq_sig=>//=; apply: depfunext=>?; rewrite seqL. Qed.

  Fact Functor_seqR : has_seqR (Functor.type 𝒞 𝒟) _ Functor_idn Functor_seq.
  Proof. by move=> F G f; apply: eq_sig=>//=; apply: depfunext=>?; rewrite seqR. Qed.

  Fact Functor_seqA : has_seqA (Functor.type 𝒞 𝒟) _ Functor_seq.
  Proof. by move=> F G H I FG GH HI; apply: eq_sig=>//=; apply: depfunext=>?; rewrite seqA. Qed.

  HB.instance Definition _ := IsCategory.Build (Functor.type 𝒞 𝒟) Functor_seqL Functor_seqR Functor_seqA.
End FunctorCategory.


Section ConstantDiagram.
  Context (𝒞 : Category.type) {𝒟 : Category.type} (d : 𝒟).

  Definition Δ : 𝒞 → 𝒟 := λ _, d.

  Definition Δ_fmap x y : x ~> y → Δ x ~> Δ y.
  Proof. by move=> ?; apply: idn. Defined.

  HB.instance Definition Δ_prefunctor_axioms := IsPrefunctor.Build 𝒞 𝒟 Δ Δ_fmap.

  Fact Δ_fmap_id : has_fmap_id Δ Δ_fmap.
  Proof. by []. Qed.

  Fact Δ_fmap_seq : has_fmap_seq Δ Δ_fmap.
  Proof. by move=> x y z f g; rewrite /Δ_fmap seqL. Qed.

  HB.instance Definition Δ_functor_axioms := IsFunctor.Build 𝒞 𝒟 Δ Δ_fmap_id Δ_fmap_seq.

  (* HB.pack doesn't work for morphism classes *)
  Definition Δ_packed : Functor.type 𝒞 𝒟.
  Proof.
    exists Δ, Δ_prefunctor_axioms.
    apply: Δ_functor_axioms.
  Defined.

End ConstantDiagram.

Record Cone {𝒞 𝒟} (F : Functor.type 𝒞 𝒟) :=
  {cone_apex : 𝒟;
   cone_legs : Δ_packed 𝒞 cone_apex ~> F}.

Record Cocone {𝒞 𝒟} (F : Functor.type 𝒞 𝒟) :=
  {cocone_apex : 𝒟;
   cocone_legs : F ~> Δ_packed 𝒞 cocone_apex}.
