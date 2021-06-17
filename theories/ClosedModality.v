(** EXPERIMENTAL. This file is a mess, don't look at it! LOL *)

From Domains Require Import Preamble Preorder Poset Dcpo DcpoProduct.

Axiom T : Dcpo.type → Prop → Dcpo.type.

(** It is a result of Jung that DCPO is cocomplete, constructively. Hence the following exists. *)
Section Modality.
  Context {A : Dcpo.type} {ϕ : Prop}.
  Axiom seal : A → T A ϕ.
  Axiom seal_cont : is_continuous seal.
  Axiom pt : ϕ → T A ϕ.
  Axiom gl : ∀ u : ϕ, ∀ x : T A ϕ, x = pt u.

  Context {C : Dcpo.type}.

  Axiom unseal : ∀ (f : A → C) (g : ϕ → C), (∀ x y, f x = g y) → is_continuous f → T A ϕ → C.

  Context {f : A → C} {g : ϕ → C} {coh : ∀ x y, f x = g y} {fcont : is_continuous f}.
  Axiom unseal_cont : is_continuous (unseal f g coh fcont).
  Axiom unseal_seal : ∀ a, unseal f g coh fcont (seal a) = f a.
  Axiom unseal_pt : ∀ z, unseal f g coh fcont (pt z) = g z.
  Axiom unseal_uniq : ∀ h, is_continuous h → (∀ x, h (seal x) = f x) → (∀ x, h (pt x) = g x) → ∀ x, h x = unseal f g coh fcont x.
End Modality.

Context (A : Dcppo.type) (ϕ : Prop).

