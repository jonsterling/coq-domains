(** EXPERIMENTAL. This file is a mess, don't look at it! LOL *)

From Domains Require Import Preamble Preorder Poset Dcpo DcpoProduct OrderSpace.

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

Lemma seal_bot_aux_sl : A → Rel (T A ϕ).
Proof.
  move=> a.
  exists (seal ⊥, seal a); cbn.
  by apply/continuous_to_monotone/bottom_is_bottom/seal_cont.
Defined.

Lemma seal_bot_aux_sl' : A → prod (T A ϕ) (T A ϕ).
Proof.
  move=> a.
  by apply/pi/seal_bot_aux_sl/a.
Defined.

Lemma seal_bot_aux_sl'_cont : is_continuous seal_bot_aux_sl'.
Proof.
  split.
  - move=> //= u; split; cbn; auto.
    apply: continuous_to_monotone; [apply: seal_cont | apply: dlub_is_ub].
  - move=> //= p H; split; cbn.
    + case: (nonempty _ h) => i _.
      apply: ltT'.
      * case: (H i)=> h1 _.
        exact: h1.
      * done.
    + apply: above_lub.
      * apply: seal_cont.
      * move=> //= z.
        specialize (H z).
        case: H => ? H.
        exact: H.
Qed.

Lemma seal_bot_aux_sl_cont : is_continuous seal_bot_aux_sl.
Proof.
  split.
  - move=> //= u; split; cbn; auto.
    by apply/continuous_to_monotone/dlub_is_ub/seal_cont.
  - move=> //= p H; split; cbn.
    + case: (nonempty _ h) => i _.
      apply: ltT'.
      * case: (H i)=> h1 _.
        exact: h1.
      * done.
    + apply: above_lub.
      * apply: seal_cont.
      * move=> //= z.
        specialize (H z).
        case: H => ? H.
        exact: H.
Qed.

Definition seal_bot_aux_pt : ϕ → Rel (T A ϕ).
Proof.
  move=> x.
  exists (pt x, pt x); cbn.
  apply: ltR.
Defined.

Definition seal_bot_aux_pt' : ϕ → prod (T A ϕ) (T A ϕ).
Proof. move=> x; by apply/pi/seal_bot_aux_pt/x. Defined.

Lemma seal_bot_aux_gl : ∀ (x : A) (y : ϕ), seal_bot_aux_sl x = seal_bot_aux_pt y.
Proof.
  move=> x y.
  apply: eq_sig; auto; cbn.
  by rewrite (gl y (seal x)) (gl y (seal ⊥)).
Qed.

Lemma seal_bot_aux_gl' : ∀ (x : A) (y : ϕ), seal_bot_aux_sl' x = seal_bot_aux_pt' y.
Proof.
  move=> x y.
  rewrite /seal_bot_aux_sl' /seal_bot_aux_sl /seal_bot_aux_pt' //=.
  by rewrite (gl y (seal x)) (gl y (seal ⊥)).
Qed.

Definition seal_bot_aux : T A ϕ → Rel (T A ϕ).
Proof.
  unshelve apply: unseal.
  - apply: seal_bot_aux_sl.
  - apply: seal_bot_aux_pt.
  - apply: seal_bot_aux_gl.
  - apply: seal_bot_aux_sl_cont.
Defined.

Definition seal_bot_aux' : T A ϕ → prod (T A ϕ) (T A ϕ).
Proof.
  unshelve apply: unseal.
  - apply: seal_bot_aux_sl'.
  - apply: seal_bot_aux_pt'.
  - apply: seal_bot_aux_gl'.
  - apply: seal_bot_aux_sl'_cont.
Defined.

(** The following lemma can't be proved in this style because the projection map [pi] is not continuous. *)
Lemma seal_bot : is_bottom (@seal A ϕ ⊥).
Proof.
  have: {h : T A ϕ → Rel (T A ϕ) | ∀ x, pi _ (h x) = (seal ⊥, x) }.
  - unshelve esplit.
    + apply: seal_bot_aux.
    + move=> x.
      replace (seal ⊥, x) with (seal_bot_aux' x).
      * rewrite /seal_bot_aux'.
        apply: (unseal_uniq (fun x => pi (T A ϕ) (seal_bot_aux x))).
        -- apply: is_continuous_cmp.
           ++ apply: unseal_cont.
           ++ admit.
              (* "pi" is continuous, from OrderSpace *)
        -- move=> ?; by rewrite /seal_bot_aux unseal_seal.
        -- move=> ?; by rewrite /seal_bot_aux unseal_pt.
      * rewrite /seal_bot_aux'; symmetry.
        apply: (unseal_uniq (λ x, (seal ⊥, x))).
        -- apply: pair_left_continous.
        -- move=> a.
           by rewrite /seal_bot_aux_sl' /seal_bot_aux_sl.
        -- move=> z.
           by rewrite /seal_bot_aux_pt' /seal_bot_aux_pt (gl z (seal ⊥)).
  - move=> [h h'] x.
    specialize (h' x).
    have h'' := (rel _ (h x)).
    rewrite /pi1 /pi2 in h''.
    by rewrite h' in h''.
Admitted.
