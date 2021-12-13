From Domains Require Import Preamble.

Unset Printing Notations.
Unset Printing Implicit.

HB.mixin Record IsGraph (obj : Type) :=
  {hom : obj → obj → Type}.

Check IsGraph.phant_axioms.

HB.structure Definition Graph := {𝒞 of IsGraph 𝒞}.

Infix "~>" := hom (at level 10).

HB.mixin Record IsPrecategory 𝒞 of IsGraph 𝒞 :=
  {idn : ∀ x : 𝒞, x ~> x;
   seq : ∀ x y z : 𝒞, x ~> y → y ~> z → x ~> z}.

HB.structure Definition Precategory := {𝒞 of IsPrecategory 𝒞 & IsGraph 𝒞}.

Arguments seq {𝒞} [x] [y] [z] f g : rename.


Section Properties.
  Context (𝒞 : Type) (hom : 𝒞 → 𝒞 → Type) (idn : ∀ x : 𝒞, hom x x) (seq : ∀ x y z : 𝒞, hom x y → hom y z → hom x z).

  Definition has_seqL := ∀ (x y : 𝒞) (f : hom x y), seq _ _ _ (idn x) f = f.
  Definition has_seqR := ∀ (x y : 𝒞) (f : hom x y), seq _ _ _ f (idn y) = f.
  Definition has_seqA := ∀ (u v w x : 𝒞) (f : hom u v) (g : hom v w) (h : hom w x), seq _ _ _ (seq _ _ _ f g) h = seq _ _ _ f (seq _ _ _ g h).
End Properties.

HB.mixin Record IsCategory 𝒞 of Precategory 𝒞 :=
  {seqL : has_seqL 𝒞 hom idn seq;
   seqR : has_seqR 𝒞 hom idn seq;
   seqA : has_seqA 𝒞 hom seq}.

HB.structure Definition Category := {𝒞 of IsCategory 𝒞 & IsPrecategory 𝒞 & IsGraph 𝒞}.
