Require Import Preamble.
Require Import Preorder.

HB.mixin Record PosetOfPreorder A of Preorder A :=
  {ltE : ∀ x y : A, x ≤ y → y ≤ x → x = y}.

HB.structure Definition Poset := {A of PosetOfPreorder A & Preorder A}.

#[export]
Hint Resolve ltR : core.

Section Extrema.
  Context {A : Poset.type}.
  Definition is_bottom (x : A) := ∀ y : A, x ≤ y.
  Definition is_top (x : A) := ∀ y : A, y ≤ x.

  Lemma bottom_is_unique : ∀ x y, is_bottom x → is_bottom y → x = y.
  Proof.
    move=> x y xb yb.
    apply: ltE.
    - apply: xb.
    - apply: yb.
  Qed.

  Lemma top_is_unique : ∀ x y, is_top x → is_top y → x = y.
  Proof.
    move=> x y xt yt.
    apply: ltE.
    - apply: yt.
    - apply: xt.
  Qed.
End Extrema.

HB.mixin Record PointedPosetOfPoset A of Poset A :=
  {ltHasBot : ∃ x : A, is_bottom x}.

HB.structure Definition PointedPoset := {A of PointedPosetOfPoset A & Poset A}.

HB.mixin Record BoundedPosetOfPointedPoset A of PointedPoset A :=
  {ltHasTop : ∃ x : A, is_top x}.

HB.structure Definition BoundedPoset := {A of BoundedPosetOfPointedPoset A & PointedPoset A}.

Section Bottom.
  Context {A : PointedPoset.type}.

  Definition bottom_bundled : {x : A | is_bottom x}.
  Proof.
    apply: constructive_definite_description.
    case: (@ltHasBot A) => x xbot.
    exists x; split; first by done.
    move=> y ybot.
    by apply: bottom_is_unique.
  Qed.

  Definition bottom : A := proj1_sig bottom_bundled.
  Definition bottom_is_bottom : is_bottom bottom := proj2_sig bottom_bundled.
  Opaque bottom.
End Bottom.

Section Top.
  Context {A : BoundedPoset.type}.

  Definition top_bundled : {x : A | is_top x}.
  Proof.
    apply: constructive_definite_description.
    case: (@ltHasTop A) => x xtop.
    exists x; split; first by done.
    move=> y ytop.
    by apply: top_is_unique.
  Qed.

  Definition top : A := proj1_sig top_bundled.
  Definition top_is_top : is_top top := proj2_sig top_bundled.
  Opaque top.
End Top.

Notation "⊥" := bottom.
Notation "⊤" := top.

Record Family (A : Type) :=
  {fam_ix : Type;
   fam_val :> fam_ix → A}.

Arguments fam_ix [_].
Arguments fam_val [_] _.

Section DirectedFamilies.
  Context {A : Poset.type} (F : Family A).

  Definition is_nonempty : Prop :=
    ∃ x : fam_ix F, True.

  Definition is_predirected : Prop :=
    ∀ i j : fam_ix F,
      ∃ k,
        F i ≤ F k ∧ F j ≤ F k.

  Record is_directed : Prop :=
    {nonempty : is_nonempty;
     predirected : is_predirected}.
End DirectedFamilies.


Section Lub.
  Context {A : Poset.type} (F : Family A).

  Definition is_ub (x : A) :=
    ∀ i, F i ≤ x.

  Record is_lub (x : A) :=
    {lub_is_ub : is_ub x;
     lub_univ : ∀ z : A, is_ub z → x ≤ z}.

  Lemma lub_unique : ∀ x y : A, is_lub x → is_lub y → x = y.
  Proof. move=> ? ? [? ?] [? ?]; apply: ltE; auto. Qed.

  Lemma above_lub : ∀ x y : A, is_lub x → (∀ z, F z ≤ y) → x ≤ y.
  Proof. move=> x y [H0 H1] H2; apply: H1 H2. Qed.
End Lub.
