Require Import Preamble.
Require Import Preorder.
Require Import Poset.

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
    exists x; split; first by done.
    move=> y ylub.
    apply: lub_unique; by eauto.
  Qed.

  Definition dlub : D.
  Proof. case: dlub_bundled => x _; exact: x. Defined.

  Lemma dlub_is_lub : is_lub A dlub.
  Proof. rewrite /dlub; by case: dlub_bundled. Qed.

  Lemma dlub_is_ub : is_ub A dlub.
  Proof. rewrite /dlub; case: dlub_bundled => ? [? ?]; auto. Qed.

  Lemma dlub_least : ∀ z : D, is_ub A z → dlub ≤ z.
  Proof. rewrite /dlub; case: dlub_bundled => ? [? ?]; auto. Qed.

  Opaque dlub.
End DLub.


#[global]
Hint Extern 0 => apply: dlub_is_lub : core.


Definition push_fam {D E : Poset.type} (f : D → E) (F : Family D) : Family E.
Proof.
  exists (fam_ix F).
  move=> i.
  apply: f.
  exact: (F i).
Defined.

Definition is_continuous {D E : Dcpo.type} (f : D → E) :=
  ∀ (A : Family D) (h : is_directed A),
    is_lub (push_fam f A) (f (dlub A h)).

Definition leq_family {D : Dcpo.type} (x y : D) : Family D.
  exists bool; case.
  - exact: x.
  - exact: y.
Defined.

Lemma leq_family_directed {D : Dcpo.type} : ∀ x y : D, x ≤ y → is_directed (leq_family x y).
Proof. move=> *; split; repeat case; try (by [exists true] + by [exists false]). Qed.

Lemma leq_to_lub {D : Dcpo.type} : ∀ x y : D, ∀ p : x ≤ y, y = dlub (leq_family x y) (leq_family_directed x y p).
Proof.
  move=> x y xy.
  apply: (lub_unique (leq_family x y)); auto.
  split.
  - case; [auto | apply: ltR].
  - move=> z hz.
    apply: hz false.
Qed.


Lemma continuous_to_monotone {D E : Dcpo.type} (f : D → E) : is_continuous f → ∀ x y, x ≤ y → f x ≤ f y.
Proof.
  move=> fcont x y p.
  rewrite (leq_to_lub x y p).
  case: (fcont (leq_family x y) (leq_family_directed x y p)) => ub _.
  apply: ub true.
Qed.
