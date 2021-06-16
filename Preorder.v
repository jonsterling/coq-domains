Require Import ssreflect Unicode.Utf8.
From HB Require Import structures.
Require Import Coq.Logic.Description Coq.Logic.PropExtensionality.


Set Primitive Projections.

Declare Scope preorder_scope.
Delimit Scope preorder_scope with P.

Open Scope preorder_scope.

HB.mixin Record PreorderOfType A :=
  {lt : A → A → Prop;
   ltR : ∀ x, lt x x;
   ltT : ∀ x y z, lt x y → lt y z → lt x z}.

HB.structure Definition Preorder := {A of PreorderOfType A}.

Infix "≤" := lt : preorder_scope.

HB.mixin Record PosetOfPreorder A of Preorder A :=
  {ltE : ∀ x y : A, x ≤ y → y ≤ x → x = y}.

HB.structure Definition Poset := {A of PosetOfPreorder A & Preorder A}.


Section Bottom.
  Context {A : Poset.type}.
  Definition is_bottom (x : A) := ∀ y : A, x ≤ y.

  Lemma bottom_is_unique : ∀ x y, is_bottom x → is_bottom y → x = y.
  Proof.
    move=> x y xb yb.
    apply: ltE.
    - apply: xb.
    - apply: yb.
  Qed.
End Bottom.

HB.mixin Record PointedPosetOfPoset A of Poset A :=
  {ltHasBot : ∃ x : A, is_bottom x}.

HB.structure Definition PointedPoset := {A of PointedPosetOfPoset A & Poset A}.

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

Notation "⊥" := bottom.

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

  Definition is_lub (x : A) :=
    is_ub x ∧
    ∀ z : A, is_ub z → x ≤ z.

  Lemma lub_unique : ∀ x y : A, is_lub x → is_lub y → x = y.
  Proof. move=> ? ? [? ?] [? ?]; apply: ltE; auto. Qed.
End Lub.

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

  Opaque dlub.
End DLub.

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

HB.mixin Record ContinuousMapOfFunction (D E : Dcpo.type) (f : D → E) :=
  {map_continuous : is_continuous f}.

HB.structure Definition ContinuousMap (D E : Dcpo.type) := {f of ContinuousMapOfFunction D E f}.

Module Σ.
  Definition Σ := Prop.
  Definition Σ_lt (x y : Σ) := x → y.
  Lemma Σ_ltR : ∀ x : Σ, x → x.
  Proof. auto. Qed.
  Lemma Σ_ltT : ∀ x y z : Σ, (x → y) → (y → z) → x → z.
  Proof. auto. Qed.

  HB.instance Definition Σ_preorder_axioms := PreorderOfType.Build Σ Σ_lt Σ_ltR Σ_ltT.

  Lemma Σ_ltE : ∀ x y : Σ, (x ≤ y) → (y ≤ x) → x = y.
  Proof. move=> *; apply: propositional_extensionality; by split. Qed.

  HB.instance Definition Σ_poset_axioms := PosetOfPreorder.Build Σ Σ_ltE.

  Lemma Σ_ltHasDLubs : ∀ (A : Family Σ), is_directed A → ∃ x, is_lub A x.
  Proof.
    move=> A dir //=.
    exists (∃ x, A x).
    split; simpl.
    - rewrite /is_ub //=.
      by intuition; compute; eauto.
    - move=> z zub; move=> [? ?].
      by apply: zub; eauto.
  Qed.

  HB.instance Definition Σ_dcpo_axioms := DcpoOfPoset.Build Σ Σ_ltHasDLubs.

  Lemma Σ_ltHasBot : ∃ x : Σ, is_bottom x.
  Proof. exists False; by move=> ?. Qed.

  HB.instance Definition Σ_pointed_poset_axioms := PointedPosetOfPoset.Build Σ Σ_ltHasBot.
End Σ.
