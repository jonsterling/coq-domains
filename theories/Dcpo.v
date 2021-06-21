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



Definition preserves_dlub {D : Dcpo.type} {E : Poset.type} (f : D → E) :=
  ∀ (A : Family D) (h : is_directed A),
    is_lub (push_fam f A) (f (dlub A h)).

Definition leq_family {D : Dcpo.type} (x y : D) : Family D.
Proof. by exists bool; case; [exact: x | exact: y]. Defined.

Lemma leq_family_directed {D : Dcpo.type} : ∀ x y : D, x ≤ y → is_directed (leq_family x y).
Proof.
  move=> *; split; first by exists true.
  by do 2!case; exists false.
Qed.

Lemma leq_to_lub {D : Dcpo.type} : ∀ x y : D, ∀ p : x ≤ y, y = dlub (leq_family x y) (leq_family_directed x y p).
Proof.
  move=> x y xy.
  apply/lub_unique/dlub_is_lub; split; first by case.
  by move=> z /(_ false).
Qed.

Lemma preserves_dlub_cont {D E : Dcpo.type} {f : D → E} : preserves_dlub f → is_continuous f.
Proof.
  rewrite /preserves_dlub.
  move=> fcont A dirA x xlub.
  replace x with (dlub A dirA).
  - apply: fcont.
  - apply: lub_unique; auto.
Qed.

Lemma cont_preserves_dlub {D : Dcpo.type} {E : Poset.type} {f : D → E} : is_continuous f → preserves_dlub f.
Proof. by move=> fcont ? ?; apply: fcont. Qed.


Lemma cont_mono {D : Dcpo.type} {E : Poset.type} (f : D → E) : is_continuous f → is_monotone f.
Proof.
  move=> /cont_preserves_dlub fdlub x y xy.
  rewrite (leq_to_lub _ _ xy).
  case: (fdlub (leq_family x y) (leq_family_directed x y xy))=> + _.
  by move/(_ true).
Qed.
