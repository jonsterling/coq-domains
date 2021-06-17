From Domains Require Import Preamble Preorder Poset.

HB.mixin Record DcpoOfPoset D of Poset D :=
  {ltHasDirLubs : ∀ (A : Family D), is_directed A → ∃ x, is_lub A x}.

HB.structure Definition Dcpo := {D of DcpoOfPoset D & Poset D}.
HB.structure Definition Dcppo := {D of Dcpo D & PointedPoset D}.

Section DLub.
  Context {D : Dcpo.type} (A : Family D) (dir : is_directed A).

  Definition dlub_bundled : {x : D | is_lub A x}.
  Proof.
    apply: constructive_definite_description.
    case: (ltHasDirLubs A dir) => //= x xlub.
    exists x; split=>// y ylub.
    by apply: (lub_unique A).
  Qed.

  Definition dlub : D.
  Proof. by case: dlub_bundled. Defined.

  Lemma dlub_is_lub : is_lub A dlub.
  Proof. by rewrite /dlub; case: dlub_bundled. Qed.

  Lemma dlub_is_ub : is_ub A dlub.
  Proof. by rewrite /dlub; case: dlub_bundled => ? []. Qed.

  Lemma dlub_least : ∀ z : D, is_ub A z → dlub ≤ z.
  Proof. by rewrite /dlub; case: dlub_bundled => ? []. Qed.

  Opaque dlub.
End DLub.


#[global]
Hint Extern 0 => apply: dlub_is_lub : core.


Definition push_fam {D E : Poset.type} (f : D → E) (F : Family D) : Family E.
Proof.
  exists (fam_ix F).
  by move=>?; apply/f/F.
Defined.

Definition is_continuous' {D E : Poset.type} (f : D → E) :=
  ∀ (A : Family D) (h : is_directed A) x,
    is_lub A x →
    is_lub (push_fam f A) (f x).

(** TODO: let's replace this with the above. *)
Definition is_continuous {D E : Dcpo.type} (f : D → E) :=
  ∀ (A : Family D) (h : is_directed A),
    is_lub (push_fam f A) (f (dlub A h)).

Definition is_monotone {D E : Poset.type} (f : D → E) :=
  ∀ x y, x ≤ y → f x ≤ f y.



Definition leq_family {D : Dcpo.type} (x y : D) : Family D.
  by exists bool; case; [exact: x | exact: y].
Defined.

Lemma leq_family_directed {D : Dcpo.type} : ∀ x y : D, x ≤ y → is_directed (leq_family x y).
Proof.
  move=> *; split; first by exists true.
  by do 2!case; exists false.
Qed.

Lemma leq_to_lub {D : Dcpo.type} : ∀ x y : D, ∀ p : x ≤ y, y = dlub (leq_family x y) (leq_family_directed x y p).
Proof.
  move=> x y xy.
  apply: (lub_unique (leq_family x y)); last by apply: dlub_is_lub.
  split; first by case.
  by move=> z /(_ false).
Qed.

Lemma continuous_to_monotone {D E : Dcpo.type} (f : D → E) : is_continuous f → is_monotone f.
Proof.
  move=> fcont x y p.
  rewrite (leq_to_lub x y p).
  case: (fcont (leq_family x y) (leq_family_directed x y p))=> + _.
  by move/(_ true).
Qed.

Lemma monotone_preserves_directed {D E : Dcpo.type} {A : Family D} {f : D → E} : is_monotone f → is_directed A → is_directed (push_fam f A).
Proof.
  move=> mono dirA.
  split.
  + rewrite /is_nonempty /push_fam //=.
    apply: nonempty dirA.
  + move=> //= u v.
    case: (predirected A dirA u v) => k [uk vk].
    by exists k; split; apply: mono.
Qed.

Lemma relax_continuous {D E : Dcpo.type} {f : D → E} : is_continuous f → is_continuous' f.
Proof.
  rewrite /is_continuous.
  move=> fcont A dirA x xlub.
  replace x with (dlub A dirA).
  - apply: fcont.
  - apply: lub_unique; auto.
Qed.

Lemma is_continuous_cmp {D E F : Dcpo.type} (f : D → E) (g : E → F) : is_continuous f → is_continuous g → is_continuous (λ x, g (f x)).
Proof.
  move=> fcont gcont; split.
  - move=> //= i.
    apply: continuous_to_monotone; first by auto.
    apply: (lub_is_ub _ _ (fcont A h)).
  - move=> z H.
    apply: lub_univ.
    + pose gcont' := relax_continuous gcont.
      apply: gcont'; last by auto.
      apply: monotone_preserves_directed; last by auto.
      by apply: continuous_to_monotone.
    + done.
Qed.
